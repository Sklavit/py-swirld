# coding=utf-8
# Copyright 2017-01-03 Sergii Nechuiviter
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""This is wrapper around PyNacl which fix it flawed API."""

# from __future__ import absolute_import, division, print_function
#
# import six
#
# from nacl import encoding
#
# import nacl.bindings
# from nacl.public import (PrivateKey as _Curve25519_PrivateKey,
#                          PublicKey as _Curve25519_PublicKey)
# from nacl.utils import StringFixer, random
from nacl import encoding
from nacl.signing import SignedMessage as pynacl_SignedMessage, \
    VerifyKey as pynacl_VerifyKey, SigningKey as pynacl_SigningKey


class SignedMessage(pynacl_SignedMessage):
    """
    A bytes subclass that holds a messaged that has been signed by a
    :class:`SigningKey`.
    """
    pass


class VerifyKey(pynacl_VerifyKey):
    """
    The public key counterpart to an Ed25519 SigningKey for producing digital
    signatures.

    :param key: [:class:`bytes`] Serialized Ed25519 public key
    :param encoder: A class that is able to decode the `key`
    """

    def __bytes__(self):
        return self._key

    def __str__(self):
        return "{}...".format(self.encode(encoding.Base64Encoder).decode('utf8')[:6])

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        return self._key == other._key

    def __hash__(self):
        return hash(self._key)


class SigningKey(pynacl_SigningKey):
    """
    Private key for producing digital signatures using the Ed25519 algorithm.

    Signing keys are produced from a 32-byte (256-bit) random seed value. This
    value can be passed into the :class:`~nacl.signing.SigningKey` as a
    :func:`bytes` whose length is 32.

    .. warning:: This **must** be protected and remain secret. Anyone who knows
        the value of your :class:`~nacl.signing.SigningKey` or it's seed can
        masquerade as you.

    :param seed: [:class:`bytes`] Random 32-byte value (i.e. private key)
    :param encoder: A class that is able to decode the seed

    :ivar: verify_key: [:class:`~nacl.signing.VerifyKey`] The verify
        (i.e. public) key that corresponds with this signing key.
    """
    def __init__(self, seed, encoder=encoding.RawEncoder):
        super(SigningKey, self).__init__(seed, encoder)
        self.verify_key = VerifyKey(self.verify_key._key, encoder=encoding.RawEncoder)

    def __bytes__(self):
        return self._seed

    def __str__(self):
        return "SigningKey(seed={})".format(self.encode(encoding.Base64Encoder).decode('utf8'))

    def __repr__(self):
        return self.__str__()

    def __eq__(self, other):
        return self._seed == other._seed

    def __hash__(self):
        return hash(self._seed)
