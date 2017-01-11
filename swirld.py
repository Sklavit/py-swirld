# coding=utf-8
# -*- coding: utf-8 -*-
import datetime
import pickle
from collections import namedtuple, defaultdict
from random import choice
from time import time, sleep
from itertools import zip_longest
from functools import reduce

from pickle import loads

from nacl.hash import sha512
from pickle import dumps

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


class Event(object):

    def __init__(self, d, parents, t=None):
        self.d = d
        self.parents = parents
        self.t = datetime.datetime.now() if t is None else t
        self.verify_key = None  # NOTE: previously c
        self.signature = None   # NOTE: previously s

    @property
    def body(self):
        return pickle.dumps((self.d, self.parents, self.t, self.verify_key))

    def sign(self, signing_key):
        self.verify_key = signing_key.verify_key
        signature = signing_key.sign(self.body).signature  # detached signature
        self.signature = signature

    def __getstate__(self):
        return self.d, self.parents, self.t, self.verify_key, self.signature

    def __setstate__(self, state):
        self.d, self.parents, self.t, self.verify_key, self.signature = state

    @property
    def sha512(self):
        return sha512(pickle.dumps(self))


class Trilean:
    false = 0
    true = 1
    undetermined = 2


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
    - connect to Node
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
        self.network = None  # {pk -> Node.ask_sync} dict
        self.n = None
        self.stake = None
        self.tot_stake = None
        self.min_s = None  # min stake amount

        # {event-hash => event}: this is the hash graph
        self.hg = {}
        # event-hash: latest event from me
        self.head = None
        # {event-hash => round-num}: assigned round number of each event
        self.round = {}
        # {event-hash}: events for which final order remains to be determined
        self.tbd = set()
        # [event-hash]: final order of the transactions
        self.transactions = []
        self.idx = {}
        # {round-num}: rounds where famousness is fully decided
        self.consensus = set()
        # {event-hash => {event-hash => bool}}
        self.votes = defaultdict(dict)
        # {round-num => {member-pk => event-hash}}: 
        self.witnesses = defaultdict(dict)
        self.famous = {}

        # {event-hash => int}: 0 or 1 + max(height of parents) (only useful for
        # drawing, it may move to viz.py)
        self.height = {}
        # {event-hash => {member-pk => event-hash}}: stores for each event ev
        # and for each member m the latest event from m having same round
        # number as ev that ev can see
        self.can_see = {}

        # init first local event
        event = self.new_event(None, ())
        h = event.sha512
        self.add_event(event)
        self.round[h] = 0
        self.witnesses[0][event.verify_key] = h
        self.can_see[h] = {event.verify_key: h}
        self.head = h

    @classmethod
    def create(cls):
        """Creates new node.
        Generate singing and verification keys. ID will be as verification kay."""
        signing_key = SigningKey.generate()
        return cls(signing_key)

    def set(self, network, n_nodes, stake):
        self.network = network  # {pk -> Node.ask_sync} dict
        self.n = n_nodes
        self.stake = stake
        self.tot_stake = sum(stake.values())
        self.min_s = 2 * self.tot_stake / 3  # min stake amount

    @property
    def id(self):
        return self.signing_key.verify_key

    def new_event(self, d, parents):
        """Create a new event.
        Access hash from class."""
        # TODO replace assert with raise Exception
        assert parents == () or len(parents) == 2  # 2 parents
        assert parents == () or self.hg[parents[0]].verify_key == self.id  # first exists and is self-parent
        assert parents == () or self.hg[parents[1]].verify_key != self.id  # second exists and not self-parent
        # TODO: fail if an ancestor of p[1] from creator self.pk is not an
        # ancestor of p[0]

        ev = Event(d, parents)
        ev.sign(self.signing_key)

        return ev

    def is_valid_event(self, h, event: Event):
        try:
            # crypto_sign_verify_detached(ev.s, dumps(ev[:-1]), ev.c)
            event.verify_key.verify(event.body, event.signature)
        except ValueError:
            return False

        return (event.sha512 == h
                and (event.parents == ()
                     or (len(event.parents) == 2
                         and event.parents[0] in self.hg and event.parents[1] in self.hg
                         and self.hg[event.parents[0]].verify_key == event.verify_key
                         and self.hg[event.parents[1]].verify_key != event.verify_key)))

        # TODO: check if there is a fork (rly need reverse edges?)
        # and all(self.hg[x].verify_key != ev.verify_key
        #        for x in self.preds[ev.parents[0]]))))

    def add_event(self, ev: Event):
        h = ev.sha512
        self.hg[h] = ev
        self.tbd.add(h)
        if ev.parents == ():
            self.height[h] = 0
        else:
            self.height[h] = max(self.height[parent] for parent in ev.parents) + 1

    def sync(self, node_id, payload):
        """Update hg and return new event ids in topological order."""

        message = dumps({c: self.height[h] for c, h in self.can_see[self.head].items()})
        signed_message = self.signing_key.sign(message)
        signed_reply = self.network[node_id](self.id, signed_message)
        serialized_reply = node_id.verify(signed_reply)

        remote_head, remote_hg = loads(serialized_reply)
        new = tuple(toposort(remote_hg.keys() - self.hg.keys(),
                             lambda u: remote_hg[u].parents))

        for h in new:
            ev = remote_hg[h]
            if self.is_valid_event(h, ev):
                self.add_event(ev)  # (, h) ??

        if self.is_valid_event(remote_head, remote_hg[remote_head]):
            ev = self.new_event(payload, (self.head, remote_head))
            self.add_event(ev)
            self.head = ev.sha512
            h = ev.sha512

        return new + (h,)

    def ask_sync(self, pk, info):
        """Respond to someone wanting to sync (only public method)."""

        # TODO: only send a diff? maybe with the help of self.height
        # TODO: thread safe? (allow to run while mainloop is running)

        msg = pk.verify(info)
        cs = loads(msg)  #crypto_sign_open(info, pk))

        subset = {h: self.hg[h] for h in bfs(
            (self.head,),
            lambda u: (p for p in self.hg[u].parents
                       if self.hg[p].verify_key not in cs or self.height[p] > cs[self.hg[p].verify_key]))}
        msg = dumps((self.head, subset))
        # return crypto_sign(msg, self.sk)
        return self.signing_key.sign(msg)

    def ancestors(self, c):
        while True:
            yield c
            if not self.hg[c].parents:
                return
            c = self.hg[c].parents[0]

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
        return a is not None and (b is None or self.height[a] >= self.height[b])

    def divide_rounds(self, events):
        """Restore invariants for `can_see`, `witnesses` and `round`.

        :param events: topologicaly sorted sequence of new event to process.
        """

        for h in events:
            ev = self.hg[h]
            if ev.parents == ():  # this is a root event
                self.round[h] = 0
                self.witnesses[0][ev.verify_key] = h
                self.can_see[h] = {ev.verify_key: h}
            else:
                r = max(self.round[p] for p in ev.parents)

                # recurrence relation to update can_see
                p0, p1 = (self.can_see[p] for p in ev.parents)
                self.can_see[h] = {c: self.maxi(p0.get(c), p1.get(c))
                                   for c in p0.keys() | p1.keys()}

                # count distinct paths to distinct nodes
                hits = defaultdict(int)
                for c, k in self.can_see[h].items():
                    if self.round[k] == r:
                        for c_, k_ in self.can_see[k].items():
                            if self.round[k_] == r:
                                hits[c_] += self.stake[c]
                # check if i can strongly see enough events
                if sum(1 for x in hits.values() if x > self.min_s) > self.min_s:
                    self.round[h] = r + 1
                else:
                    self.round[h] = r
                self.can_see[h][ev.verify_key] = h
                if self.round[h] > self.round[ev.parents[0]]:
                    self.witnesses[self.round[h]][ev.verify_key] = h

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

        for r_, y in iter_voters():

            hits = defaultdict(int)
            for c, k in self.can_see[y].items():
                if self.round[k] == r_ - 1:
                    for c_, k_ in self.can_see[k].items():
                        if self.round[k_] == r_ - 1:
                            hits[c_] += self.stake[c]
            s = {self.witnesses[r_ - 1][c] for c, n in hits.items()
                 if n > self.min_s}

            for r, x in iter_undetermined(r_):
                if r_ - r == 1:
                    self.votes[y][x] = x in s
                else:
                    v, t = majority((self.stake[self.hg[w].verify_key], self.votes[w][x]) for w in s)
                    if (r_ - r) % C != 0:
                        if t > self.min_s:
                            self.famous[x] = v
                            done.add(r)
                        else:
                            self.votes[y][x] = v
                    else:
                        if t > self.min_s:
                            self.votes[y][x] = v
                        else:
                            # the 1st bit is same as any other bit right? # TODO not!
                            self.votes[y][x] = bool(self.hg[y].signature[0] // 128)

        new_c = {r for r in done
                 if all(w in self.famous for w in self.witnesses[r].values())}
        self.consensus |= new_c
        return new_c

    def find_order(self, new_c):
        to_int = lambda x: int.from_bytes(self.hg[x].signature, byteorder='big')

        for r in sorted(new_c):
            f_w = {w for w in self.witnesses[r].values() if self.famous[w]}
            white = reduce(lambda a, b: a ^ to_int(b), f_w, 0)
            ts = {}
            seen = set()
            for x in bfs(filter(self.tbd.__contains__, f_w),
                         lambda u: (p for p in self.hg[u].parents if p in self.tbd)):
                c = self.hg[x].verify_key
                s = {w for w in f_w if c in self.can_see[w]
                     and self.higher(self.can_see[w][c], x)}
                if sum(self.stake[self.hg[w].verify_key] for w in s) > self.tot_stake / 2:
                    self.tbd.remove(x)
                    seen.add(x)
                    times = []
                    for w in s:
                        a = w
                        while (c in self.can_see[a]
                               and self.higher(self.can_see[a][c], x)
                               and self.hg[a].parents):
                            a = self.hg[a].p[0]
                        times.append(self.hg[a].t)
                    times.sort()
                    ts[x] = .5 * (times[len(times) // 2] + times[(len(times) + 1) // 2])
            final = sorted(seen, key=lambda x: (ts[x], white ^ to_int(x)))
            for i, x in enumerate(final):
                self.idx[x] = i + len(self.transactions)
            self.transactions += final
        if self.consensus:
            print(self.consensus)

    def main(self):
        """Main working loop."""

        new = ()
        while True:
            payload = (yield new)

            # pick a random node to sync with but not me
            node_id = tuple(self.network.keys() - {self.id})[randrange(self.n - 1)]
            new = self.sync(node_id, payload)
            self.divide_rounds(new)

            new_c = self.decide_fame()
            self.find_order(new_c)


def run_network(n_nodes, n_turns):
    nodes = [HashgraphNetNode.create() for i in range(n_nodes)]
    stake = {node.id: 1 for node in nodes}
    network = {}
    for node in nodes:
        node.set(network, n_nodes, stake)  # TODO make network creation explicit !
        
    for n in nodes:
        network[n.id] = n.ask_sync
    mains = [n.main() for n in nodes]
    for m in mains:
        next(m)
    for i in range(n_turns):
        r = randrange(n_nodes)
        print('working node: %i, event number: %i' % (r, i))
        next(mains[r])
    return nodes

if __name__ == '__main__':
    run_network(3, 10)
