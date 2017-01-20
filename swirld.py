# coding=utf-8
# -*- coding: utf-8 -*-
import base64
import datetime
import pickle

from collections import namedtuple, defaultdict
from multiprocessing import Process, Queue
from pprint import pformat
from queue import Empty
from random import choice
from time import time, sleep
from itertools import zip_longest
from functools import reduce

from pickle import loads

import logging

import copy
from nacl.bindings import crypto_hash_sha512
from nacl.encoding import Base64Encoder
from nacl.hash import sha512
from pickle import dumps

from profilehooks import profile

from sklavit_nacl.signing import SigningKey
from utils import bfs, toposort, randrange

C = 6


def majority(it):
    hits = [0, 0]
    for s, x in it:
        hits[int(x)] += s
    if hits[0] > hits[1]:
        return False, hits[0]
    else:
        return True, hits[1]


class Event(object):  # TODO make it namedtuple
    """Event is a node of hashgraph."""

    def __init__(self, signing_key, d, parents, t=None):
        # Immutable body of Event
        self.d = d
        self.parents = parents
        self.t = datetime.datetime.now() if t is None else t
        self.verify_key = signing_key.verify_key  # Setting of verify_key is delayed TODO fix it!
        # End of immutable body
        parents_ids = [parent.id for parent in self.parents]
        self.__body = pickle.dumps((self.d, parents_ids, self.t, self.verify_key))

        # Sign Event body.
        self.signature = signing_key.sign(self.__body).signature

        # Compute Event hash and ID.
        h = Base64Encoder.encode(crypto_hash_sha512(self.__body)).decode()
        self.__id = h[:5]  # TODO fix this limit

        # assigned round number of each event
        self.round = None

        # {event-hash => bool}
        self.votes = dict()  # TODO only votes are Graph node-specific????

        # 0 or 1 + max(height of parents)
        if parents == ():
            self.height = 0
        else:
            self.height = max(parent.height for parent in parents) + 1

        # {node-id = > event}}: stores for each event ev
        # and for each member m the latest event from m having same round
        # number as ev that ev can see
        self.can_see = {}

    def __str__(self):
        return "{{Event}}{}... by {}, H{}, R{}, P{}, D{}".format(
            self.id[:6], self.verify_key, self.height, self.round, [p.id for p in self.parents], self.d)

    def __repr__(self):
        return self.__str__()

    @property
    def body(self):
        return self.__body

    @property
    def id(self):
        return self.__id


class Trilean:
    false = 0
    true = 1
    undetermined = 2


class Hashgraph:
    def __init__(self):
        self.stake = None
        self.tot_stake = None
        self.min_s = None  # min stake amount

        # {event-hash => event}: this is the hash graph
        self.lookup_table = {}

        # event-hash: latest event from me
        self.head = None

        # {event-hash => round-num}: assigned round number of each event
        # self.round = {}

        # {event-hash}: events for which final order remains to be determined
        self.tbd = set()

        # [event-hash]: final order of the transactions
        self.transactions = []

        self.idx = {}

        # {round-num}: rounds where famousness is fully decided
        self.consensus = set()

        # {event-hash => {event-hash => bool}}
        # self.votes = defaultdict(dict)

        # {round-num => {member-pk => event-hash}}:
        self.witnesses = defaultdict(dict)

        self.famous = {}

        # {event-hash => int}: 0 or 1 + max(height of parents)
        # self.height = {}

        # {event-hash => {member-pk => event-hash}}: stores for each event ev
        # and for each member m the latest event from m having same round
        # number as ev that ev can see
        # self.can_see = {}

    def add_first_event(self, event):
        self.add_event(event)
        event.round = 0  # TODO move to event creation ?
        self.witnesses[0][event.verify_key] = event
        event.can_see = {event.verify_key: event}  # TODO move to event creation ?
        self.head = event

    def add_event(self, event: Event):
        """Add given event to this hashgraph."""
        h = event.id
        self.lookup_table[h] = event
        self.tbd.add(h)  # TODO add event?

        logging.info("{}.add_event: {}".format(self, event))

    def set_stake(self, stake):
        self.stake = stake
        self.tot_stake = sum(stake.values())
        self.min_s = 2 * self.tot_stake / 3  # min stake amount

    def create_first_event(self, signing_key):
        event = self._new_event(None, (), signing_key)
        return event

    def new_event(self, payload, other_parent, creator_id):
        event = self._new_event(payload, (self.head, other_parent), creator_id)
        return event

    def _new_event(self, d, parents, signing_key):
        """Create a new event.
        Access hash from class.
        :param creator_id: """
        # TODO: fail if an ancestor of p[1] from creator self.pk is not an ancestor of p[0] ???
        event = Event(signing_key, d, parents)
        logging.info("{}._new_event: {}".format(self, event))
        return event

    def is_valid_event(self, id, event: Event):
        try:
            event.verify_key.verify(event.body, event.signature)
        except ValueError:
            return False

        return (event.id == id
                and (event.parents == ()
                     or (len(event.parents) == 2
                         and event.parents[0].id in self.lookup_table and event.parents[1].id in self.lookup_table
                         and event.parents[0].verify_key == event.verify_key
                         and event.parents[1].verify_key != event.verify_key)))

        # TODO: check if there is a fork (rly need reverse edges?)
        # and all(x.verify_key != ev.verify_key
        #        for x in self.preds[ev.parents[0]]))))

    def get_fingerprint(self):
        """Returns dict of heights for each branch (== HashgraghNetNode)."""
        return {branch_id: event.height for branch_id, event in self.head.can_see.items()}

    def keys(self):
        return self.lookup_table.keys()

    def difference(self, info):
        """Difference with given hashgraf info (fingerprint?)"""
        # NOTE we need bfs() due to cheating possibility -- several children of one parent
        # succ = lambda u: (p for p in u.parents
        #                if (p.verify_key not in info) or (p.height > info[p.verify_key]))
        def succ(u):
            return [p for p in u.parents
                    if (p.verify_key not in info) or (p.height > info[p.verify_key])]

        subset = [h
                  for h in bfs((self.head,), succ)]
        return subset

    def ancestors(self, c):
        while True:
            yield c
            if not c.parents:
                return
            c = c.parents[0]

    def maxi(self, a, b):
        if self.higher(a, b):
            return a
        else:
            return b

    def _higher(self, a, b):
        for x, y in zip_longest(self.ancestors(a), self.ancestors(b)):
            if x == b or y is None:
                return True
            elif y == a or x is None:
                return False

    def higher(self, a, b):
        return a is not None and (b is None or a.height >= b.height)

    def divide_rounds(self, events):
        """Restore invariants for `can_see`, `witnesses` and `round`.

        :param events: topologicaly sorted sequence of new event to process.
        """

        for h in events:
            ev = h
            if ev.parents == ():  # this is a root event
                h.round = 0
                self.witnesses[0][ev.verify_key] = h
                h.can_see = {ev.verify_key: h}
            else:
                r = max(p.round for p in ev.parents)

                # recurrence relation to update can_see
                p0, p1 = (p.can_see for p in ev.parents)
                h.can_see = {c: self.maxi(p0.get(c), p1.get(c))
                             for c in p0.keys() | p1.keys()}

                # count distinct paths to distinct nodes
                hits = defaultdict(int)
                for c, k in h.can_see.items():
                    if k.round == r:
                        for c_, k_ in k.can_see.items():
                            if k_.round == r:
                                hits[c_] += self.stake[c]
                # check if i can strongly see enough events
                if sum(1 for x in hits.values() if x > self.min_s) > self.min_s:
                    h.round = r + 1
                else:
                    h.round = r
                h.can_see[ev.verify_key] = h
                if h.round > ev.parents[0].round:
                    self.witnesses[h.round][ev.verify_key] = h

    def decide_fame(self):
        max_r = max(self.witnesses)
        max_c = 0
        while max_c in self.consensus:
            max_c += 1

        # helpers to keep code clean
        def iter_undetermined(r_):
            for r in range(max_c, r_):
                if r not in self.consensus:
                    for w in self.witnesses[r].values():
                        if w not in self.famous:
                            yield r, w

        def iter_voters():
            for r_ in range(max_c + 1, max_r + 1):
                for w in self.witnesses[r_].values():
                    yield r_, w

        done = set()

        for r_, y in iter_voters():  # type: int, Event

            hits = defaultdict(int)
            for c, k in y.can_see.items():
                if k.round == r_ - 1:
                    for c_, k_ in k.can_see.items():
                        if k_.round == r_ - 1:
                            hits[c_] += self.stake[c]
            s = {self.witnesses[r_ - 1][c] for c, n in hits.items()
                 if n > self.min_s}

            for r, x in iter_undetermined(r_):
                if r_ - r == 1:
                    y.votes[x] = x in s
                else:
                    v, t = majority((self.stake[self.lookup_table[w].verify_key], w.votes[x]) for w in s)
                    if (r_ - r) % C != 0:
                        if t > self.min_s:
                            self.famous[x] = v
                            done.add(r)
                        else:
                            y.votes[x] = v
                    else:
                        if t > self.min_s:
                            y.votes[x] = v
                        else:
                            # the 1st bit is same as any other bit right? # TODO not!
                            y.votes[x] = bool(y.signature[0] // 128)

        new_c = {r for r in done
                 if all(w in self.famous for w in self.witnesses[r].values())}
        self.consensus |= new_c
        return new_c

    def find_order(self, new_c):
        to_int = lambda x: int.from_bytes(self.lookup_table[x].signature, byteorder='big')

        for r in sorted(new_c):
            f_w = {w for w in self.witnesses[r].values() if self.famous[w]}
            white = reduce(lambda a, b: a ^ to_int(b), f_w, 0)
            ts = {}
            seen = set()
            for x in bfs(filter(self.tbd.__contains__, f_w),
                         lambda u: (p for p in self.lookup_table[u].parents if p in self.tbd)):
                c = self.lookup_table[x].verify_key
                s = {w for w in f_w if c in w.can_see
                     and self.higher(w.can_see[c], x)}
                if sum(self.stake[self.lookup_table[w].verify_key] for w in s) > self.tot_stake / 2:
                    self.tbd.remove(x)
                    seen.add(x)
                    times = []
                    for w in s:
                        a = w
                        while (c in a.can_see
                               and self.higher(a.can_see[c], x)
                               and self.lookup_table[a].parents):
                            a = self.lookup_table[a].p[0]
                        times.append(self.lookup_table[a].t)
                    times.sort()
                    ts[x] = .5 * (times[len(times) // 2] + times[(len(times) + 1) // 2])
            final = sorted(seen, key=lambda x: (ts[x], white ^ to_int(x)))
            for i, x in enumerate(final):
                self.idx[x] = i + len(self.transactions)
            self.transactions += final
        if self.consensus:
            print(self.consensus)

class HashgraphNetNode:
    """A node in a hashgraph network.

    Note can:
    - process incoming requests.
    - generate requests

    Node <==> Node <==> User

    Network == set of working Nodes

    Node -- User:
    - create
    - dump/load identity
    - start (and connect to network), ready to process requests
    - shutdown
    -----
    - acquaint with Node
    - forget Node
    -----
    - get (full) state; get consensus as sub-request
    - send message
    - subscribe / unsubscribe listener
    -----

    Node -- Node:
    - ping ?; return ping time
    - get( what to get ?); returns response
    - post(message); returns response
    - pinged_get
    - pinged_post


    """
    def __init__(self, signing_key):
        self.signing_key = signing_key  # TODO implement

        self.neighbours = {}   # dict(pk -> Node)

        self.hashgraph = Hashgraph()

        # init first local event
        event = self.hashgraph.create_first_event(self.signing_key)
        self.hashgraph.add_first_event(event)

        self.new = []  # list of messages

    @property
    def n(self):
        return len(self.neighbours) + 1

    @classmethod
    def create(cls):
        """Creates new node.
        Generate singing and verification keys. ID will be as verification kay."""
        signing_key = SigningKey.generate()
        return cls(signing_key)

    def set(self, stake):
        self.hashgraph.set_stake(stake)

    def acquaint(self, node):
        """- acquaint with Node"""
        self.neighbours[node.id] = node

    def forget(self, node):
        """Forget neighbour node."""
        del self.neighbours[node.id]

    @property
    def id(self):
        return self.signing_key.verify_key

    def __str__(self):
        return "Node({})".format(self.id)

    def sync(self, node, payload):
        """Update hg and return new event ids in topological order."""

        fingerprint = self.hashgraph.get_fingerprint()

        logging.info("{}.sync:message = \n{}".format(self, pformat(fingerprint)))

        # NOTE: communication channel security must be provided in standard way: SSL
        logging.info("{}.sync: reply acquired:".format(self))

        remote_head, difference = node.ask_sync(self, fingerprint)
        logging.info("  remote_head = {}".format(remote_head))
        logging.info("  difference  = {}".format(difference))

        # TODO move to hashgraph
        new = tuple(toposort([event for event in difference if event.id not in self.hashgraph.lookup_table],  # difference.keys() - self.hashgraph.keys(),
                             lambda u: u.parents))

        logging.info("{}.sync:new = \n{}".format(self, pformat(new)))

        # TODO move to hashgraph
        for event in new:
            if self.hashgraph.is_valid_event(event.id, event):  # TODO check?
                self.hashgraph.add_event(event)  # (, h) ??

        # TODO move to hashgraph
        # TODO check DOUBLE add remote_head ?
        if self.hashgraph.is_valid_event(remote_head.id, remote_head):  # TODO move id check to communication part
            event = self.hashgraph.new_event(payload, remote_head, self.signing_key)
            self.hashgraph.add_event(event)
            self.hashgraph.head = event
            h = event.id

        logging.info("{}.sync exits.".format(self))

        return new + (event,)

    def ask_sync(self, node, fingerprint):
        """Respond to someone wanting to sync (only public method)."""

        # TODO: only send a diff? maybe with the help of self.height
        # TODO: thread safe? (allow to run while mainloop is running)

        subset = self.hashgraph.difference(fingerprint)

        # TODO Clear response from internal information !!!

        return self.hashgraph.head, subset

    def heartbeat_callback(self):
        """Main working loop."""

        logging.info("{}.heartbeat...".format(self))

        # payload = [event.id for event in self.new]
        payload = ()  # TODO: it is not used!!! why?
        self.new = []

        logging.info("{}.payload = {}".format(self, payload))

        # pick a random node to sync with but not me
        node = choice(list(self.neighbours.values()))

        logging.info("{}.sync with {}".format(self, node))
        new = self.sync(node, payload)

        logging.info("{}.new = {}".format(self, new))

        self.new = list(new)

        self.hashgraph.divide_rounds(new)

        new_c = self.hashgraph.decide_fame()
        self.hashgraph.find_order(new_c)

        logging.info("{}.new_c = {}".format(self, new_c))
        logging.info("{}.heartbeat exits.".format(self))

        # return payload
        return self.new


class LocalNetwork(object):

    def __init__(self, n_nodes):
        """Creates local network with given number of nodes."""
        self.size = n_nodes
        nodes = [HashgraphNetNode.create() for i in range(n_nodes)]
        stake = {node.id: 1 for node in nodes}
        for node in nodes:
            node.set(stake)  # TODO make network creation explicit !

        self.nodes = nodes
        for node in self.nodes:
            for other_node in self.nodes:
                if node != other_node:
                    node.acquaint(other_node)

        self.ids = {node.id: i for i, node in enumerate(nodes)}

        self.heartbeat_callbacks = [n.heartbeat_callback for n in self.nodes]

    def get_random_node(self):
        i = randrange(self.size)
        return self.nodes[i]


def run_network(n_nodes, n_turns):
    network = LocalNetwork(n_nodes)

    for i in range(n_turns):
        node = network.get_random_node()
        logging.info("working node: {}, event number: {}".format(node, i))
        node.heartbeat_callback()

    return network

if __name__ == '__main__':
    logging.getLogger().setLevel(logging.DEBUG)
    run_network(3, 100)
