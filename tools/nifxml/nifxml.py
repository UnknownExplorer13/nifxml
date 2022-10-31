#!/usr/bin/python
"""
nifxml.py

Parses nif.xml into dictionaries of classes grouped by XML tag type.

This file is part of nifxml <https://www.github.com/niftools/nifxml>
Copyright (c) 2017 NifTools

This program is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, version 3.

This program is distributed in the hope that it will be useful, but
WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
General Public License for more details.

You should have received a copy of the GNU General Public License
along with this program. If not, see <http://www.gnu.org/licenses/>.

This file incorporates work covered by the following copyright and permission notice:
 Copyright (c) 2005, NIF File Format Library and Tools.
 All rights reserved.

 Redistribution and use in source and binary forms, with or without
 modification, are permitted provided that the following conditions
 are met:
   - Redistributions of source code must retain the above copyright
     notice, this list of conditions and the following disclaimer.
   - Redistributions in binary form must reproduce the above
     copyright notice, this list of conditions and the following
     disclaimer in the documentation and/or other materials provided
     with the distribution.
   - Neither the name of the NIF File Format Library and Tools
     project nor the names of its contributors may be used to endorse
     or promote products derived from this software without specific
     prior written permission.
 THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 FOR A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE
 COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING,
 BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT
 LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN
 ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE
 POSSIBILITY OF SUCH DAMAGE.
"""

from __future__ import unicode_literals
from typing import Callable, Optional

from xml.dom.minidom import Attr, Document, Element, Node, parse

import os
import re
import logging

from .utility import export

#
# Globals
#

# The script will reject any versions older than this
MIN_XML_VERSION = '0.9.1.0'

XML_PATH = os.path.join(os.path.dirname(os.path.realpath(__file__)), '../../nif.xml')

TYPES_NATIVE = {'TEMPLATE': 'T'}
TYPES_BASIC = {}
TYPES_ENUM = {}
TYPES_BITFLAG = {}
TYPES_STRUCT = {}
TYPES_NIOBJECT = {}
TYPES_VERSION = {}


NAMES_BASIC = []
NAMES_STRUCT = []
NAMES_ENUM = []
NAMES_BITFLAG = []
NAMES_NIOBJECT = []
NAMES_VERSION = []


__all__ = ['TYPES_VERSION', 'TYPES_BASIC', 'TYPES_NIOBJECT', 'TYPES_STRUCT', 'TYPES_ENUM', 'TYPES_BITFLAG', 'TYPES_NATIVE',
           'NAMES_VERSION', 'NAMES_BASIC', 'NAMES_NIOBJECT', 'NAMES_STRUCT', 'NAMES_ENUM', 'NAMES_BITFLAG']


@export
def class_name(name_in: str) -> str:
    """
    Formats a valid C++ class name from the name format used in the XML.
    """
    if name_in is None:
        return None
    try:
        return TYPES_NATIVE[name_in]
    except KeyError:
        return name_in.replace(' ', '_').replace(":", "_")


@export
def define_name(name_in: str) -> str:
    """
    Formats an all-uppercase version of the name for use in C++ defines.
    """
    name_out = ''
    for i, char in enumerate(name_in):
        if char.isupper():
            if i > 0:
                name_out += '_'
                name_out += char
            else:
                name_out += char
        elif char.islower() or char.isdigit():
            name_out += char.upper()
        else:
            name_out += '_'
    return name_out


@export
def member_name(name_in: str) -> str:
    """
    Formats a version of the name for use as a C++ member variable.
    """
    if name_in is None or name_in == 'ARG':
        return name_in
    name_out = ''
    lower = True
    for char in name_in:
        if char == ' ':
            lower = False
        elif char.isalnum():
            if lower:
                name_out += char.lower()
            else:
                name_out += char.upper()
                lower = True
        elif char == '\\':  # arg member access operator
            name_out += '.'
        else:
            name_out += '_'
            lower = True
    return name_out


@export
def version2number(s: str) -> int:
    """
    Translates a legible NIF version number to the packed-byte numeric representation.
    For example, "10.0.1.0" is translated to 0x0A000100.
    """
    if not s:
        return None

    numbers = s.split('.')
    if len(numbers) > 4:
        assert False
        return int(s)

    if len(numbers) == 2:
        version = 0
        version += int(numbers[0]) << (3 * 8)
        if len(numbers[1]) >= 1:
            version += int(numbers[1][0]) << (2 * 8)
        if len(numbers[1]) >= 2:
            version += int(numbers[1][1]) << (1 * 8)
        if len(numbers[1]) >= 3:
            version += int(numbers[1][2:])
        return version
    else:
        version = 0
        for i, ver in enumerate(numbers):
            version += int(ver) << ((3 - i) * 8)
        return version


@export
def scanBrackets(expr_str: str, from_index: int = 0) -> tuple[int, int]:
    """Looks for matching brackets.

    >>> scanBrackets('abcde')
    (-1, -1)
    >>> scanBrackets('()')
    (0, 1)
    >>> scanBrackets('(abc(def))g')
    (0, 9)
    >>> s = '  (abc(dd efy 442))xxg'
    >>> startpos, endpos = scanBrackets(s)
    >>> print s[startpos+1:endpos]
    abc(dd efy 442)
    """
    startpos = -1
    endpos = -1
    scandepth = 0
    for scanpos in range(from_index, len(expr_str)):
        scanchar = expr_str[scanpos]
        if scanchar == "(":
            if startpos == -1:
                startpos = scanpos
            scandepth += 1
        elif scanchar == ")":
            scandepth -= 1
            if scandepth == 0:
                endpos = scanpos
                break
    else:
        if startpos != -1 or endpos != -1:
            raise ValueError("expression syntax error (non-matching brackets?)")
    return (startpos, endpos)

class Expression:
    """This class represents an expression.

    >>> class A(object):
    ...     x = False
    ...     y = True
    >>> a = A()
    >>> e = Expression('x || y')
    >>> e.eval(a)
    1
    >>> Expression('99 & 15').eval(a)
    3
    >>> bool(Expression('(99&15)&&y').eval(a))
    True
    >>> a.hello_world = False
    >>> def nameFilter(s):
    ...     return 'hello_' + s.lower()
    >>> bool(Expression('(99 &15) &&WoRlD', name_filter = nameFilter).eval(a))
    False
    >>> Expression('c && d').eval(a)
    Traceback (most recent call last):
        ...
    AttributeError: 'A' object has no attribute 'c'
    >>> bool(Expression('1 == 1').eval())
    True
    >>> bool(Expression('1 != 1').eval())
    False
    """
    operators = ['==', '!=', '>=', '<=', '&&', '||', '&', '|', '-', '+', '>', '<', '/', '*']

    def __init__(self, expr_str: str, name_filter: Callable[[str],str] = None):
        self._code = expr_str
        left, self._op, right = self._partition(expr_str)
        self._left = self._parse(left, name_filter)
        if right:
            self._right = self._parse(right, name_filter)
        else:
            self._right = ''

    def eval(self, data=None):
        """Evaluate the expression to an integer."""

        if isinstance(self._left, Expression):
            left = self._left.eval(data)
        elif isinstance(self._left, str):
            left = getattr(data, self._left) if self._left != '""' else ""
        else:
            assert isinstance(self._left, int)  # debug
            left = self._left

        if not self._op:
            return left

        if isinstance(self._right, Expression):
            right = self._right.eval(data)
        elif isinstance(self._right, str):
            right = getattr(data, self._right) if self._right != '""' else ""
        else:
            assert isinstance(self._right, int)  # debug
            right = self._right

        if self._op == '==':
            return int(left == right)
        elif self._op == '!=':
            return int(left != right)
        elif self._op == '>=':
            return int(left >= right)
        elif self._op == '<=':
            return int(left <= right)
        elif self._op == '&&':
            return int(left and right)
        elif self._op == '||':
            return int(left or right)
        elif self._op == '&':
            return left & right
        elif self._op == '|':
            return left | right
        elif self._op == '-':
            return left - right
        elif self._op == '+':
            return left + right
        elif self._op == '/':
            return left / right
        elif self._op == '*':
            return left * right
        elif self._op == '!':
            return not left
        else:
            raise NotImplementedError("expression syntax error: operator '" + self._op + "' not implemented")

    def __str__(self):  # type: () -> str
        """Reconstruct the expression to a string."""

        left = str(self._left)
        if not self._op:
            return left
        right = str(self._right)
        return left + ' ' + self._op + ' ' + right

    def encode(self, encoding):  # type: (str) -> str
        """
        To allow encode() to be called on an Expression directly as if it were a string
        (For Python 2/3 cross-compatibility.)
        """
        return self.__str__().encode(encoding)

    @classmethod
    def _parse(cls, expr_str, name_filter=None):  # type: (str, Callable[[str], str]) -> str
        """Returns an Expression, string, or int, depending on the
        contents of <expr_str>."""
        # brackets or operators => expression
        if ("(" in expr_str) or (")" in expr_str):
            return Expression(expr_str, name_filter)
        for op in cls.operators:
            if expr_str.find(op) != -1:
                return Expression(expr_str, name_filter)

        mver = re.compile("[0-9]+\\.[0-9]+\\.[0-9]+\\.[0-9]+")
        iver = re.compile("[0-9]+")

        # try to convert it to an integer
        try:
            if mver.match(expr_str):
                return "0x%08X" % (version2number(expr_str))
            elif iver.match(expr_str):
                return str(int(expr_str))
        except ValueError:
            pass

        # failed, so return the string, passed through the name filter
        return name_filter(expr_str) if name_filter else expr_str

    @classmethod
    def _partition(cls, expr_str):
        """Partitions expr_str. See examples below.

        >>> Expression._partition('abc || efg')
        ('abc', '||', 'efg')
        >>> Expression._partition('abc||efg')
        ('abc', '||', 'efg')
        >>> Expression._partition('abcdefg')
        ('abcdefg', '', '')
        >>> Expression._partition(' abcdefg ')
        ('abcdefg', '', '')
        >>> Expression._partition(' (a | b) & c ')
        ('a | b', '&', 'c')
        >>> Expression._partition('(a | b)!=(b&c)')
        ('a | b', '!=', 'b&c')
        >>> Expression._partition('(a== b) &&(( b!=c)||d )')
        ('a== b', '&&', '( b!=c)||d')
        """
        # check for unary operators
        if expr_str.strip().startswith('!'):
            return expr_str.lstrip(' !'), '!', None
        lenstr = len(expr_str)
        # check if the left hand side starts with brackets
        # and if so, find the position of the starting bracket and the ending
        # bracket
        left_startpos, left_endpos = cls._scan_brackets(expr_str)
        if left_startpos >= 0:
            # yes, it is a bracketed expression
            # so remove brackets and whitespace,
            # and let that be the left hand side
            left_str = expr_str[left_startpos + 1:left_endpos].strip()

            # the next token should be the operator
            # find the position where the operator should start
            op_start_pos = left_endpos + 1
            while op_start_pos < lenstr and expr_str[op_start_pos] == " ":
                op_start_pos += 1
            if op_start_pos < lenstr:
                # to avoid confusion between && and &, and || and |,
                # let's first scan for operators of two characters
                # and then for operators of one character
                for op_end_pos in range(op_start_pos + 1, op_start_pos - 1, -1):
                    op_str = expr_str[op_start_pos:op_end_pos + 1]
                    if op_str in cls.operators:
                        break
                else:
                    raise ValueError("expression syntax error: expected operator at '%s'" % expr_str[op_start_pos:])
            else:
                return cls._partition(left_str)
        else:
            # it's not... so we need to scan for the first operator
            for op_start_pos, ch in enumerate(expr_str):
                if ch == ' ':
                    continue
                if ch == '(' or ch == ')':
                    raise ValueError("expression syntax error: expected operator before '%s'" % expr_str[op_start_pos:])
                # to avoid confusion between && and &, and || and |,
                # let's first scan for operators of two characters
                for op_end_pos in range(op_start_pos + 1, op_start_pos - 1, -1):
                    op_str = expr_str[op_start_pos:op_end_pos + 1]
                    if op_str in cls.operators:
                        break
                else:
                    continue
                break
            else:
                # no operator found, so we are done
                left_str = expr_str.strip()
                op_str = ''
                right_str = ''
                return left_str, op_str, right_str

            # operator found! now get the left hand side
            left_str = expr_str[:op_start_pos].strip()

        return left_str, op_str, expr_str[op_end_pos + 1:].strip()

    @staticmethod
    def _scan_brackets(expr_str, from_index=0):
        """Looks for matching brackets.

        >>> Expression._scan_brackets('abcde')
        (-1, -1)
        >>> Expression._scan_brackets('()')
        (0, 1)
        >>> Expression._scan_brackets('(abc(def))g')
        (0, 9)
        >>> s = '  (abc(dd efy 442))xxg'
        >>> startpos, endpos = Expression._scan_brackets(s)
        >>> print s[startpos+1:endpos]
        abc(dd efy 442)
        """
        startpos = -1
        endpos = -1
        scandepth = 0
        for scanpos in range(from_index, len(expr_str)):
            scanchar = expr_str[scanpos]
            if scanchar == "(":
                if startpos == -1:
                    startpos = scanpos
                scandepth += 1
            elif scanchar == ")":
                scandepth -= 1
                if scandepth == 0:
                    endpos = scanpos
                    break
        else:
            if startpos != -1 or endpos != -1:
                raise ValueError("expression syntax error (non-matching brackets?)")
        return (startpos, endpos)

    def code(self, prefix='', brackets=True, name_filter=None):  # type: (str, bool, Callable[[str], str]) -> str
        """Format an expression as a string."""
        lbracket = "(" if brackets else ""
        rbracket = ")" if brackets else ""
        if not self._op:
            if not self.lhs:
                return ''
            if isinstance(self.lhs, int):
                return self.lhs
            elif self.lhs in TYPES_NIOBJECT:
                return 'IsDerivedType(%s::TYPE)' % self.lhs
            else:
                return prefix + (name_filter(self.lhs) if name_filter else self.lhs)
        elif self._op == '!':
            lhs = self.lhs
            if isinstance(lhs, Expression):
                lhs = lhs.code(prefix, True, name_filter)
            elif lhs in TYPES_NIOBJECT:
                lhs = 'IsDerivedType(%s::TYPE)' % lhs
            elif lhs and not lhs.isdigit() and not lhs.startswith('0x'):
                lhs = prefix + (name_filter(lhs) if name_filter else lhs)
            return '%s%s%s%s' % (lbracket, self._op, lhs, rbracket)
        else:
            lhs = self.lhs
            if isinstance(lhs, Expression):
                lhs = lhs.code(prefix, True, name_filter)
            elif lhs in TYPES_NIOBJECT:
                lhs = 'IsDerivedType(%s::TYPE)' % lhs
            elif lhs and not lhs.isdigit() and not lhs.startswith('0x'):
                lhs = prefix + (name_filter(lhs) if name_filter else lhs)

            rhs = self.rhs
            if isinstance(rhs, Expression):
                rhs = rhs.code(prefix, True, name_filter)
            elif rhs in TYPES_NIOBJECT:
                rhs = 'IsDerivedType(%s::TYPE)' % rhs
            elif rhs and not rhs.isdigit() and not rhs.startswith('0x'):
                rhs = prefix + (name_filter(rhs) if name_filter else rhs)
            return '%s%s %s %s%s' % (lbracket, lhs, self._op, rhs, rbracket)

    def get_terminals(self):
        """Return all terminal names (without operators or brackets)."""
        if isinstance(self.lhs, Expression):
            for terminal in self.lhs.get_terminals():
                yield terminal
        elif self.lhs:
            yield self.lhs
        if isinstance(self.rhs, Expression):
            for terminal in self.rhs.get_terminals():
                yield terminal
        elif self.rhs:
            yield self.rhs

    def __getattr__(self, name):
        if name == 'lhs':
            return getattr(self, '_left')
        if name == 'rhs':
            return getattr(self, '_right')
        if name == 'op':
            return getattr(self, '_op')
        return object.__getattribute__(self, name)

    def isdigit(self):
        """ducktyping: pretend we're also a string with isdigit() method"""
        return False


class Expr(Expression):
    """
    Represents a mathmatical expression?
    @ivar lhs: The left hand side of the expression?
    @ivar clhs: The C++ formatted version of the left hand side of the expression?
    @ivar op: The operator used in the expression.  ==, &&, !=, etc.
    @ivar rhs: The right hand side of the expression?
    """

    def __init__(self, expr_str: str , name_filter=None):
        Expression.__init__(self, expr_str, name_filter)

    def code(self, prefix: str = '', brackets=True, name_filter: Callable[[str],str]=None):
        if not name_filter:
            name_filter = member_name
        return Expression.code(self, prefix, brackets, name_filter)


class Option:
    """This class represents an option in an option list."""

    def __init__(self, element:Element):
        """This constructor converts an XML <option> element into an Option object."""
        assert element.tagName == 'option'

        # member attributes
        self.value = element.getAttribute('value')
        """The C++ value of option variable.  Comes from the "value" attribute of the <option> tag."""
        self.name = element.getAttribute('name')
        """The name of this member variable.  Comes from the "name" attribute of the <option> tag."""
        self.description: str = self.name
        """The description of this option.  Comes from the text between <option> and </option>."""

        # TODO: figure what this does to document it
        if element.firstChild:
            assert element.firstChild.nodeType == Node.TEXT_NODE
            self.description = element.firstChild.nodeValue.strip()
        
        self.cname = self.name.upper().replace(" ", "_").replace("-", "_").replace("/", "_").replace("=", "_").replace( ":", "_")
        """The name of this member for use in C++."""


@export
class Field:
    """This class represents the nif.xml <add> tag."""

    def __init__(self, element: Element):
        """
        This constructor converts an XML <field> element into a Member object.
        Some sort of processing is applied to the various variables that are copied from the XML tag...
        Seems to be trying to set reasonable defaults for certain types, and put things into C++ format generally.
        """
        assert element.tagName == 'field'

        # member attributes
        self.name: str = element.getAttribute('name')
        """The name of this member variable. Comes from the "name" attribute of the <add> tag."""
        self.suffix = element.getAttribute('suffix')
        self.type = element.getAttribute('type')
        self.arg = element.getAttribute('arg')
        """The argument of this member variable.  Comes from the "arg" attribute of the <add> tag."""
        self.template: str = element.getAttribute('template')
        """The template type of this member variable.  Comes from the "template" attribute of the <add> tag."""
        self.length: Expr = Expr(element.getAttribute('length'))
        """The first array size of this member variable.  Comes from the "length" attribute of the <add> tag."""
        self.width: Expr = Expr(element.getAttribute('width'))
        """The first array size of this member variable.  Comes from the "width" attribute of the <add> tag."""
        self.cond: Expr = Expr(element.getAttribute('cond'))
        """The condition of this member variable.  Comes from the "cond" attribute of the <add> tag."""
        self.func: str = element.getAttribute('function')
        """The function of this member variable.  Comes from the "func" attribute of the <add> tag."""
        self.default: str = element.getAttribute('default')
        """The default value of this member variable.  Comes from the "default" attribute of the <add> tag. Formatted to be ready to use in a C++ constructor initializer list."""
        self.orig_since: str = element.getAttribute('since')
        self.orig_until: str = element.getAttribute('until')
        self.since: int = version2number(element.getAttribute('since'))
        """The first version this member exists.  Comes from the "since" attribute of the <add> tag."""
        self.until: int = version2number(element.getAttribute('until'))
        """The last version this member exists.  Comes from the "until" attribute of the <add> tag."""
        xint = lambda s: int(s) if s else None
        self.userver: Optional[int] = xint(element.getAttribute('userver'))
        """The user version where this member exists.  Comes from the "userver" attribute of the <add> tag."""
        self.userver2: Optional[int] = xint(element.getAttribute('userver2'))
        """The user version 2 where this member exists.  Comes from the "userver2" attribute of the <add> tag."""
        self.vercond: Expr = Expr(element.getAttribute('vercond'))
        """The version condition of this member variable.  Comes from the "vercond" attribute of the <add> tag."""
        self.is_public: bool = (element.getAttribute('public') == "1")
        """Whether this member will be declared public.  Comes from the "public" attribute of the <add> tag."""
        self.is_abstract: bool = (element.getAttribute('abstract') == "1")
        """Whether this member is abstract.  This means that it does not factor into read/write."""
        self.next_dup: Optional[Field] = None
        """Next duplicate member"""
        self.is_manual_update: bool = False
        """True if the member value is manually updated by the code"""
        self.is_calculated: bool = (element.getAttribute('calculated') == "1")

        # Get description from text between start and end tags
        self.description: str = ""
        """The description of this member variable.  Comes from the text between <add> and </add>."""
        if element.firstChild:
            assert element.firstChild.nodeType == Node.TEXT_NODE
            self.description = element.firstChild.nodeValue.strip()
        elif self.name.lower().find("unk") == 0:
            self.description = "Unknown."

        # Format default value so that it can be used in a C++ initializer list
        if not self.default and (not self.length.lhs and not self.width.lhs):
            if self.type in ["unsigned int", "unsigned short", "byte", "int", "short", "char"]:
                self.default = "0"
            elif self.type == "bool":
                self.default = "false"
            elif self.type in ["Ref", "Ptr"]:
                self.default = "NULL"
            elif self.type in "float":
                self.default = "0.0"
            elif self.type == "HeaderString":
                pass
            elif self.type == "Char8String":
                pass
            elif self.type == "StringOffset":
                self.default = "-1"
            elif self.type in NAMES_BASIC:
                self.default = "0"
            elif self.type in NAMES_BITFLAG or self.type in NAMES_ENUM:
                self.default = "0"
        if self.default:
            if self.default[0] == '(' and self.default[-1] == ')':
                self.default = self.default[1:-1]
            if self.length.lhs:  # handle static array types
                if self.length.lhs.isdigit():
                    sep = (',(%s)' % class_name(self.type))
                    self.default = self.length.lhs + sep + sep.join(self.default.split(' ', int(self.length.lhs)))
            elif self.type == "string" or self.type == "IndexString":
                self.default = "\"" + self.default + "\""
            elif self.type == "float":
                # Cast to float then back to string to add any missing ".0"
                self.default = str(float(self.default)) + "f"
            elif self.type in ["Ref", "Ptr", "bool", "Vector3"]:
                pass
            elif self.default.find(',') != -1:
                pass
            else:
                self.default = "(%s)%s" % (class_name(self.type), self.default)

        self.uses_argument: bool = self.cond.lhs == '(ARG)' or self.length.lhs == '(ARG)' or self.width.lhs == '(ARG)'
        """Specifies whether this attribute uses an argument."""

        self.type_is_native: bool = self.name in TYPES_NATIVE
        """true if the type is implemented natively"""

        self.is_duplicate: bool = False
        """true if this is a duplicate of a previously declared member"""

        # true if width refers to an array
        self.width_dynamic: bool = False
        """Specifies whether width refers to an array (?)"""


        sib = element.previousSibling
        while sib:
            if sib.nodeType == Node.ELEMENT_NODE:
                sis_name = sib.getAttribute('name')
                if sis_name == self.name and not self.suffix:
                    self.is_duplicate = True
                sis_length = Expr(sib.getAttribute('length'))
                sis_width = Expr(sib.getAttribute('width'))
                if sis_name == self.width.lhs and sis_length.lhs:
                    self.width_dynamic = True
            sib = sib.previousSibling

        # Calculate stuff from reference to next members
        self.length_ref: list[str] = []
        """# Names of the attributes it is a (unmasked) size of"""
        self.width_ref: list[str] = []
        """Names of the attributes it is a (unmasked) size of"""
        self.cond_ref: list[str] = []
        """Names of the attributes it is a condition of"""
        sib = element.nextSibling
        while sib is not None:
            if sib.nodeType == Node.ELEMENT_NODE:
                sis_name = sib.getAttribute('name')
                sis_length = Expr(sib.getAttribute('length'))
                sis_width = Expr(sib.getAttribute('width'))
                sis_cond = Expr(sib.getAttribute('cond'))
                if sis_length.lhs == self.name and (not sis_length.rhs or sis_length.rhs.isdigit()):
                    self.length_ref.append(sis_name)
                if sis_width.lhs == self.name and (not sis_width.rhs or sis_width.rhs.isdigit()):
                    self.width_ref.append(sis_name)
                if sis_cond.lhs == self.name:
                    self.cond_ref.append(sis_name)
            sib = sib.nextSibling

        # C++ names
        self.c_name: str = member_name(self.name if not self.suffix else self.name + "_" + self.suffix)
        """Unlike default, name isn't formatted for C++ so use this instead?"""
        self.c_type: str = class_name(self.type)
        """Unlike default, type isn't formatted for C++ so use this instead?"""
        self.c_arg: str = member_name(self.arg)
        """Unlike default, arg isn't formatted for C++ so use this instead?"""
        self.c_template: str = class_name(self.template)
        """Unlike default, template isn't formatted for C++ so use this instead?"""
        self.c_length_ref: list[str] = [member_name(n) for n in self.length_ref]
        """Unlike default, length_ref isn't formatted for C++ so use this instead?"""
        self.c_width_ref: list[str] = [member_name(n) for n in self.width_ref]
        """Unlike default, width_ref isn't formatted for C++ so use this instead?"""
        self.c_cond_ref: list[str] = [member_name(n) for n in self.cond_ref]
        """Unlike default, cond_ref isn't formatted for C++ so use this instead?"""


class NifXml:
    """This class represents the nif.xml <niftoolsxml> tag."""

    def __init__(self, element: Element):
        self.version: int = version2number(element.getAttribute('version'))

    def is_supported(self):  # type: () -> bool
        """If the nif.xml version meets the requirements."""
        return self.version >= version2number(MIN_XML_VERSION)


@export
class Version:
    """This class represents the nif.xml <version> tag."""

    def __str__(self):
        return self.name

    def __init__(self, element: Element):
        self.num: str = element.getAttribute('num')
        """The version raw number eg: 0.0.0.0"""
        self.name: str = element.getAttribute('id')
        """The value used to identify the version in the nif.xml file"""
        self.description: str = element.firstChild.nodeValue.strip()
        """What the version number represents in a human readable manner"""


@export
class Basic:
    """This class details a basic data type found in a <basic> tag."""

    def __init__(self, element: Element, ntypes):
        self.name: str = element.getAttribute('name')
        """The name associated with the basic type"""
        assert self.name  # name is mandatory

        self.cname: str = class_name(self.name)
        """The name that should be used in c++ files"""
        
        self.description: str = ""
        """A human readable description of the datatype"""
        if element.firstChild and element.firstChild.nodeType == Node.TEXT_NODE:
            self.description = element.firstChild.nodeValue.strip()
        elif self.name.lower().find("unk") == 0:
            self.description = "Unknown."

        self.count: str = element.getAttribute('count')
        self.template: bool = (element.getAttribute('istemplate') == "1")
        self.options: list[Option] = []

        self.is_link: bool = False
        self.is_crossref: bool = False
        self.has_links: bool = False
        self.has_crossrefs: bool = False

        self.nativetype: Optional[str] = None 
        if ntypes:
            self.nativetype = ntypes.get(self.name)
            if self.nativetype:
                TYPES_NATIVE[self.name] = self.nativetype
                if self.nativetype == "Ref":
                    self.is_link = True
                    self.has_links = True
                if self.nativetype == "*":
                    self.is_crossref = True
                    self.has_crossrefs = True


@export
class Enum(Basic):
    """This class represents the nif.xml <enum> tag."""

    def __init__(self, element: Element, ntypes: dict[str,str]):
        Basic.__init__(self, element, ntypes)

        self.storage = element.getAttribute('storage')
        self.prefix = element.getAttribute('prefix')
        # Find the native storage type
        self.storage = TYPES_BASIC[self.storage].nativetype if TYPES_BASIC[self.storage].nativetype else TYPES_BASIC[self.storage].name
        self.description = element.firstChild.nodeValue.strip()

        self.nativetype = self.cname
        TYPES_NATIVE[self.name] = self.nativetype

        # Locate all special enumeration options
        for option in element.getElementsByTagName('option'):
            if self.prefix and option.hasAttribute('name'):
                option.setAttribute('name', self.prefix + "_" + option.getAttribute('name'))
            if option.hasAttribute("bit"):
                option.setAttribute('value', option.getAttribute("bit"))
            self.options.append(Option(option))


@export
class BitFlag(Enum):
    """This class represents the nif.xml <bitflags> tag."""

    def __init__(self, element: Element , ntypes: dict[str,str]):
        Enum.__init__(self, element, ntypes)
        for option in self.options:
            option.bit = option.value
            option.value = 1 << int(option.value)


@export
class Struct(Basic):
    """This class represents the nif.xml <struct> tag."""

    def __init__(self, element:Element, ntypes: dict[str,str]):
        Basic.__init__(self, element, ntypes)

        self.members = []  # type: List[Field]
        self.argument = False  # type: bool

        # store all attribute data & calculate stuff
        for member in element.getElementsByTagName('field'):
            x = Field(member)

            # Ignore infinite recursion on already visited structs
            if x in self.members:
                continue

            self.members.append(x)

            # detect argument
            self.argument = bool(x.uses_argument)

            # detect links & crossrefs
            mem = None
            try:
                mem = TYPES_BASIC[x.type]
            except KeyError:
                try:
                    mem = TYPES_STRUCT[x.type]
                except KeyError:
                    pass
            if mem:
                if mem.has_links:
                    self.has_links = True
                if mem.has_crossrefs:
                    self.has_crossrefs = True

        # create duplicate chains for items that need it (only valid in current object scope)
        #  prefer to use iterators to avoid O(n^2) but I dont know how to reset iterators
        for outer in self.members:
            atx = False
            for inner in self.members:
                if atx:
                    if outer.name == inner.name:  # duplicate
                        outer.next_dup = inner
                        break
                elif outer == inner:
                    atx = True

    def find_field(self, name: str, inherit:bool = False) -> Optional[Field]:
        """Find member by name"""
        for mem in self.members:
            if mem.name == name:
                return mem
        return None

    def find_first_ref(self, name: str) -> Optional[Field]:
        """Find first reference of name in class."""
        for mem in self.members:
            if mem.length and mem.length.lhs == name:
                return mem
            elif mem.width and mem.width.lhs == name:
                return mem
        return None

    def has_arr(self) -> bool:
        """Tests recursively for members with an array size."""
        for mem in self.members:
            if mem.length.lhs or (mem.type in TYPES_STRUCT and TYPES_STRUCT[mem.type].has_arr()):
                return True
        return False


@export
class NiObject(Struct):
    """This class represents the nif.xml <niobject> tag."""

    def __init__(self, element, ntypes):
        Struct.__init__(self, element, ntypes)
        self.is_ancestor = (element.getAttribute('abstract') == "1")
        inherit = element.getAttribute('inherit')
        self.inherit = TYPES_NIOBJECT[inherit] if inherit else None
        self.has_interface = (element.getElementsByTagName('interface') != [])

    def find_field(self, name: str, inherit: bool=False) -> Optional[Field]:
        """Find member by name"""
        ret = Struct.find_field(self, name)
        if not ret and inherit and self.inherit:
            ret = self.inherit.find_member(name, inherit)
        return ret

    def find_first_ref(self, name: str) -> Optional[Field]:
        """Find first reference of name in class"""
        ret = None
        if self.inherit:
            ret = self.inherit.find_first_ref(name)
        if not ret:
            ret = Struct.find_first_ref(self, name)
        return ret

    def ancestors(self): # type: () -> list[NiObject]
        """List all ancestors of this block"""
        ancestors = []
        parent = self
        while parent:
            ancestors.append(parent)
            parent = parent.inherit
        return ancestors


class Token:
    """A key pair for data retrival, it's not a dictionary because it makes stuff simpler to deal with."""

    def __init__(self, tag):
        self.name: str = tag.getAttribute("token")
        """The name of the token"""
        # all vars should be formatted like #name#
        assert self.name.startswith("#") and self.name.endswith("#")
        self.value: str = tag.getAttribute("string")
        """The value that should replace the token"""



def replaceTokens(element: Element, tokenGroups: dict[str, list[Token]]):
    """Replaces tokens with their text equivalents."""

    attr: Attr
    for attr in element._attrs.values():
        if attr.name in tokenGroups:
            found = True
            while found:
                found = False
                for token in tokenGroups[attr.name]:
                    if token.name in attr.value:
                        attr.value = attr.value.replace(token.name, token.value)
                        found = True

    child: Node
    for child in element.childNodes:
        if child.nodeType == child.ELEMENT_NODE:
            replaceTokens(child, tokenGroups)



@export
def parse_xml(ntypes: dict[str,str] = None, path: str = XML_PATH) -> bool: 
    """Import elements into our NIF classes"""

    if os.path.exists(path):
        xml = parse(path) # type: Document
    else:
        raise ImportError("nif.xml not found")

    # Logger
    logging.basicConfig(level=logging.INFO)
    logger = logging.getLogger('nifxml')

    nifxml = NifXml(xml.documentElement)
    if not nifxml.is_supported():
        logger.error("The nif.xml version you are trying to parse is not supported by nifxml.py.")
        return False

    # For some reason tokens that contain other tokens are placed before those tokens.
    # It seems that this is needed for some thing that uses this functionality.
    # So let's make this a direction agnostic token list.

    # 1. Find all tokens verexpr
    tokenGroups = {} # type: dict[str, list[Token]]
    allTokens = [] # type: list[Token]
    for element in xml.getElementsByTagName('token'):
        # initialize categories if they don't already exist
        attrs = element.getAttribute('attrs').split();
        for attrType in attrs:
            tokenGroups.setdefault(attrType, [])
        # Yall should really look into setteling on a single name, it makes handling this a lot less confusing.
        for tokenTag in element.getElementsByTagName(element.getAttribute("name")):
            token = Token(tokenTag)
            for attrType in attrs:
                tokenGroups[attrType].append(token)
                allTokens.append(token)


    # 2. Replace tokens with values for tokens that contain other tokens. Repeat until no token found.
    foundToken = True
    while foundToken:
        foundToken = False
        for src in allTokens:
            for trg in allTokens:
                if trg.name in src.value:
                    src.value = src.value.replace(trg.name, trg.value)
                    foundToken = True

    #replace every token in the document
    for child in xml.documentElement.childNodes:
        if child.nodeType == xml.ELEMENT_NODE and child.tagName != "token":
            replaceTokens(child, tokenGroups)

    for element in xml.getElementsByTagName('version'):
        instance = Version(element)
        assert instance.name not in TYPES_VERSION
        TYPES_VERSION[instance.name] = instance
        NAMES_VERSION.append(instance.name)

    for element in xml.getElementsByTagName('basic'):
        instance = Basic(element, ntypes)
        assert instance.name not in TYPES_BASIC
        TYPES_BASIC[instance.name] = instance
        NAMES_BASIC.append(instance.name)

    for element in xml.getElementsByTagName('enum'):
        instance = Enum(element, ntypes)
        assert instance.name not in TYPES_ENUM
        TYPES_ENUM[instance.name] = instance
        NAMES_ENUM.append(instance.name)

    for element in xml.getElementsByTagName('bitflags'):
        instance = BitFlag(element, ntypes)
        assert instance.name not in TYPES_BITFLAG
        TYPES_BITFLAG[instance.name] = instance
        NAMES_BITFLAG.append(instance.name)

    for element in xml.getElementsByTagName('struct'):
        instance = Struct(element, ntypes)
        assert instance.name not in TYPES_STRUCT
        TYPES_STRUCT[instance.name] = instance
        NAMES_STRUCT.append(instance.name)

    for element in xml.getElementsByTagName('niobject'):
        instance = NiObject(element, ntypes)
        assert instance.name not in TYPES_NIOBJECT
        TYPES_NIOBJECT[instance.name] = instance
        NAMES_NIOBJECT.append(instance.name)

    return validate_xml()


def validate_xml():  # type: () -> bool
    """Perform some basic validation on the data retrieved from the XML"""
    val = lambda x, y: x and y and len(x) == len(y) and all(n for n in y)
    versions = val(TYPES_VERSION, NAMES_VERSION)
    basics = val(TYPES_BASIC, NAMES_BASIC)
    structs = val(TYPES_STRUCT, NAMES_STRUCT)
    blocks = val(TYPES_NIOBJECT, NAMES_NIOBJECT)
    enums = val(TYPES_ENUM, NAMES_ENUM)
    flags = val(TYPES_BITFLAG, NAMES_BITFLAG)
    res = (versions and basics and structs and blocks and enums and flags)
    if not res:
        logger = logging.getLogger('nifxml')
        logger.error("The parsing of nif.xml did not pass validation.")
    return res
