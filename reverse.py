r""".  
Python code for experimenting with the following question:

  Find all positive integers a,b such that a+b and a*b have the same number 
  of decimal digits and such that their digits are reversed from each other.

e.g., a = 3 and b = 24 gives a*b = 27 and a+b = 72

The algorithms presented here are based on the article

[1] Xander Faber and Jon Grantham. "On Integers Whose Sum is the Reverse of
    their Product". arXiv:2108.13441 [math.NT], 2021.

Some non-core functionality depends on Sage or pygraphviz.


TABLE OF CONTENTS

- UTILITIES
  - digit_string
  - string_to_int
  - string_format
  - generic_string
  - int_from_base_expansion
  - base_expansion
  - xgcd
  - gcd
  - solve_linear_congruence
  - is_rsp_pair
  - check_large_a
  - recursion_start
  - generic_recursion_start
  - construct_automata
  - construct_generic_automata

- RSPChar (class)
- RSPState (class)
- RSPAutomaton (class)

- RSPGenericChar (class)
- RSPGenericState (class)
- RSPGenericAutomaton (class)

NOTES

The primary difference between this implementation and the description in [1] is
that we have included various optimizations that were not needed for the
article. 

A priori, it seems plausible that the DFA for constructing reversed sum-product
pairs as in [1] could have multiple transitions from a state s to a state
s'. However, one can show that this is not the case. We give a representative
example of how this works. 

Proposition. Suppose that 

  (b_r, b_0, \lambda, \rho) and (b_r', b_0', \lambda, \rho) 

are two solutions to the equations defining the start of the recursion in [1],
Section 5.1. Then b_r' = b_r and b_0' = b_0. Said another way, there is only one
transition from the initial state to any carry state in the DFA.

Proof. The equations defining the start of the recursion tell us that

  a b_0  = b_r  + \rho \beta  AND  a b_r  + \lambda = a + b_0
  a b_0' = b_r' + \rho \beta  AND  a b_r' + \lambda = a + b_0'.

Subtracting these gives the equations

  a(b_0 - b_0') = b_r - b_r'  AND  a(b_r - b_r') = b_0 - b_0'.

Multiplying the first by a and subtracting the second gives

  a^2 (b_0 - b_0') = b_0 - b_0'.

It follows that either b_0 = b_0' or a = 1. In the former case, we also conclude
that b_r = b_r', as desired. The latter case contradicts the preceding
proposition unless \beta = 2. But if \beta = 2, the only value available for
b_0, b_r is 1, so we are finished in that case as well. QED

"""

from collections import defaultdict
from itertools import product
from string import ascii_lowercase, ascii_uppercase
from re import search
from math import ceil

################################################################################  
#################################  UTILITIES  ##################################
################################################################################

def digit_string(i):
  r""".
  Return the string representation of the i-th printable digit 

  INPUT:

  - ``i`` -- an integer in the interval [0,62)

  OUTPUT:

  - The string representing the `i`-th element of the list
    [0, 1, 2, ..., 9, A, B, C, ..., Z, a, b, c, ..., z]

  EXAMPLES::
   
    >>> digit_string(0)
    '0'
    >>> digit_string(61)
    'z'

  """
  if i < 0 or i >= 62:
    raise ValueError('Input {} cannot be converted to a string'.format(i))    
  if i < 10:
    return str(i)
  if i < 36:
    return ascii_uppercase[i-10]
  if i < 62:
    return ascii_lowercase[i-36]

_strings = dict([(digit_string(i),i) for i in range(62)])
def string_to_int(c):
  r"""
  Return the int corresponding to the character ``c``
  """
  return _strings.get(c)
  
#################################  UTILITIES  ##################################

def string_format(base, n):
  r"""
  Convert a list of ints into a string for given base

  INPUT:

  - ``base`` -- an integer > 1

  - ``n`` -- a list of ints in range [0,base)

  OUTPUT:

  - The string representation of ``n`` if base < 62, and ``n`` otherwise. The
    leftmost entry of ``n`` is the most significant digit. 

  EXAMPLES::

    >>> string_format(16, (13, 10, 9))
    'DA9'
    >>> string_format(16, (15, ))
    'F'

  """
  if base <= 1:
    raise ValueError('base = {} is invalid'.format(base))
  if base >= 62:
    return n
  s = ''
  msg = 'n = {} is not a valid representation of an integer in base {}'
  for d in n:
    if d >= base:
      raise ValueError(msg.format(n,base))
    s += digit_string(d)
  return s

#################################  UTILITIES  ##################################

def generic_string(pair, name):
  r"""
  Return a string representation of the affine polynomial for the  generic tuple `(u,v)`

  INPUT:

  - ``pair`` -- a pair of ints `u,v`, with `u \ge 0`

  - ``name`` -- string 

  OUTPUT:

  - If name='T', the string 'uT + v', with appropriate modifications if `u` or `v` is zero.

  EXAMPLES::

    >>> generic_string((3,1),'T')
    '3T + 1'
    >>> generic_string((3,0),'U')
    '3U'
    >>> generic_string((1,-2),'T')
    'T - 2'
    >>> generic_string((0,5),'T')
    '5'

  """
  u,v = pair
  if u == 0:
    return str(v)
  if u == 1:
    u = ''
  s = '{}{}'.format(u,name)
  if v > 0:
    s += ' + {}'.format(v)
  elif v < 0:
    s += ' - {}'.format(abs(v))
  return s

#################################  UTILITIES  ##################################

def int_from_base_expansion(base, dig_ints):
  r"""
  Return the integer n with expansion given by ``dig_ints`` in given base

  INPUT:

  - ``base`` -- an integer > 1

  - ``dig_ints`` -- a list of ints in the range [0,base), say [n_r, ..., n_0]

  OUTPUT:

  - The quantity \sum_{i=0}^r n_i base^i

  """
  return sum(bi*base**i for i,bi in enumerate(reversed(dig_ints)))

#################################  UTILITIES  ##################################

def base_expansion(base, n):
  r"""
  Return a representation of the expansion of n in given base

  INPUT:

  - ``base`` -- an integer > 1

  - ``n`` - a positive int

  OUTPUT:

  - If base <= 62, a string representing the integer n in the given
    base. Otherwise, a list of ints [n_r, ..., n_0] such that 
    n = \sum n_i base^i

  EXAMPLES:: 

    >>> base_expansion(10, 123)
    '123'
    >>> base_expansion(16, 123)
    '7B'
    >>> base_expansion(100, 123)
    [1, 23]

  """
  dig_ints = []
  while n > 0:
    nmodbase = n % base    
    dig_ints.append(nmodbase)
    n = (n - nmodbase) // base
  dig_ints.reverse()
  if base >= 62:
    return dig_ints
  return string_format(base,dig_ints)

#################################  UTILITIES  ##################################

def xgcd(a, b):
  r"""
  Return g, x, y such that ax + by = g

  INPUT:

  - ``a, b`` -- ints, not both zero

  OUTPUT:

  - A triple of ints `(g,x,y)` such that `g` is the greatest common divisor of
    `a` and `b` and `ax + by = g`.

  EXAMPLES::

    >>> xgcd(4,10)
    (2, -2, 1)

    >>> xgcd(123,4567)
    (1, 854, -23)

  """
  if a == 0 and b == 0:
    raise ValueError('gcd does not exist')  
  if a == 0 and b > 0:
    return b, 0, 1
  elif a == 0 and b < 0:
    return -b,0,-1
  else:
    g, y, x = xgcd(b % a, a)
    return g, x - (b // a) * y, y

def gcd(a,b):
  r"""
  Return the greatest common divisor of a and b
  """
  g,_,_ = xgcd(a,b)
  return g
  
#################################  UTILITIES  ##################################

def solve_linear_congruence(a, b, n, bound=None):
  r""".
  Return all solutions in [0,n) to the congruence ax = b (mod n)

  INPUT:

  - ``a, b`` -- integers

  - ``n`` -- a positive integer

  - ``bound`` -- optional positive integer

  OUTPUT:

  - A list of all solutions to the congruence ax = b (mod n) in the interval
    [0,N), where N = n if bound is None and N = bound otherwise. 

  EXAMPLES::

    >>> solve_linear_congruence(2, 2, 8)
    [1, 5]
    >>> solve_linear_congruence(2, 2, 8, 5)
    [1]

  """
  g, x, _ = xgcd(a,n)
  if b % g != 0:
    return []
  m = n // g
  x0 = ( (b//g) * x ) % m
  if bound is None:
    return [x0 + i*m for i in range(g)]
  sols = []
  while x0 < bound:
    sols.append(x0)
    x0 += m
  return sols

#################################  UTILITIES  ##################################
  
def is_rsp_pair(base, a, b):
  r""".
  Determine if `(a,b)` is a reversed sum-product pair to the given base

  INPUT:

  - ``base`` -- an integer > 1

  - ``a, b`` -- either strings representing positive integers in the given base
    or tuples of ints giving the digits of the representation of such integers
    in the given base

  OUTPUT:

  - True if a*b and a+b have reversed digits when represented in the given base.

  EXAMPLES::

    >>> is_rsp_pair(10, '3', '24')
    True
    >>> is_rsp_pair(16, '2', '6B')
    True
    >>> is_rsp_pair(16, '3', '24')
    False

  """
  if isinstance(a,str):
    a = [string_to_int(c) for c in a]
  if isinstance(b,str):
    b = [string_to_int(c) for c in b]
  na = int_from_base_expansion(base,a)
  nb = int_from_base_expansion(base,b)
  a_plus_b = base_expansion(base,na+nb)
  a_times_b = base_expansion(base,na*nb)
  return a_plus_b == a_times_b[::-1]

#################################  UTILITIES  ##################################

def check_large_a(base):
  r"""
  Verify there is no reversed sum-product pair satisfying conclusion of Lemma 3.1

  INPUT:

  - ``base`` -- an int > `

  OUTPUT:

  - A pair of ints `(a,b)` satisfying

    * `a \le b`; 

    * `base < a < 2*base`; 

    *  `b < base*(base+1)`; and

    * `(a,b)` is a reversed sum-product pair for the given base, 

    or None if no such pair exists. 

  NOTE:

  - Lemma 3.1 of [1] shows that if `a \le b` is a reversed sum-product pair for
    a given base `\beta` with `a > \beta`, then `a < 2*\beta` and `b <
    \beta*(\beta+1)`. This function verifies there is no reversed sum-product
    pair satisfying these additional constraints. We use this fact for `\beta
    \le 5` (a small amount of computation) in the proof of Proposition 3.2.

  EXAMPLES::

    >>> check_large_a(2) is None
    True
    >>> check_large_a(3) is None
    True
    >>> check_large_a(4) is None
    True
    >>> check_large_a(5) is None
    True

  """
  for a in range(base+1,2*base):
    for b in range(a,base*(base+1)):
      a_plus_b = base_expansion(base,a+b)
      a_times_b = base_expansion(base,a*b)
      if a_plus_b == a_times_b[::-1]: return(a,b)

#################################  UTILITIES  ##################################

def recursion_start(base, a=None):
  r"""
  Find solutions to the equations for starting the recursion in [1], Section 5.1

  INPUT:

  - ``base`` -- an int > 1

  - ``a`` -- optional int in the interval `[1,base)`

  OUTPUT:

  - A dict whose keys are values `a` in the interval `[1,base)` such that
    `gcd(a-1, base-1) = 1` and whose values are 4-tuples `(b_r,b_0,l,r)` 
    such that 

    * `0 < b_r < base`;

    * `0 < b_0 < base - a`;

    * `0 \le l,r < a` satisfy `b_r = ab_0 + r base` and `l = a + b_0 - ab_r`.

    If no such 4-tuple exists, that value of `a` will not appear as a key.
    
    If `a` is provided as an argument, then only that key will be considered
    when constructing the output dict. 

  EXAMPLES::

    >>> recursion_start(10)
    {2: [(4, 7, 1, 1)], 3: [(2, 4, 1, 1)]}
    >>> recursion_start(10, 2)
    {2: [(4, 7, 1, 1)]}
    >>> recursion_start(10, 5)
    {}

  """
  a_vals = defaultdict(lambda:[])
  if a is None:
    aa = range(1,base)
  else:
    aa = [a]
  for a in aa: 
    if gcd(a-1,base-1) != 1: continue
    for b0 in range(1,base-a):
      br = (a*b0) % base 
      l = a + b0 - a*br # Forces a*br + l < base
      if l < 0 or l >= a: continue
      r = (a*b0 - br) // base # Satisfies 0 <= r < a
      a_vals[a].append((br,b0,l,r))
  return dict(a_vals)

#################################  UTILITIES  ##################################

def generic_recursion_start(a, v=None):
  r"""
  Find solutions to the equations for starting the generic recursion

  INPUT:

  - ``a`` -- a positive int

  - ``v`` -- optional int in the interval `[0,a^2-1)`

  OUTPUT:

  - A dict whose keys are integers `v` in the interval `[0,a^2-1)` and whose
    values are 4-tuples `(b_r,b_0,l,r)` such that

    * `base = (a^2-1)T + v` is a 1-parameter family;

    * `b_r` is a tuple `(p,q)` such that `0 < pT + q < (a^2-1)T + v` for all
      sufficiently large `T`;

    * `b_0` is a tuple `(p,q)` such that `0 < pT + q < (a^2-1)T + v - a` for all
      sufficiently large `T`;

    * `0 \le l,r < a` satisfy `b_r = ab_0 + r base` and 
      `l = a + b_0 - ab_r`. 

    If no such 4-tuple exists, that value of `v` will not appear as a key.

  NOTE:

  - Solutions are generic in the sense that they are valid for all sufficiently
    large parameter values `T`. It is possible for a proper subset of the
    solutions to be valid for smaller values of `T`. 
    

  EXAMPLES::

    >>> generic_recursion_start(2)
    {1: [((1, 1), (2, 1), 1, 1)], 2: [((1, 2), (2, 2), 0, 1)]}
    >>> generic_recursion_start(3,3)
    {}

  """
  v_vals = defaultdict(lambda:[])
  if v is None:
    vv = range(1, a**2-1) # Residue class 0 (mod a^2 - 1) never has a solution
  else:
    vv = [v]
  u = a**2 - 1

  def is_good_pair(base,pair):
    u,v = base
    P,Q = pair
    # PT + Q > 0 for T >> 0
    if P < 0: return False
    if P == 0 and Q <= 0: return False
    # PT + Q < uT + v for T >>0
    if P > u: return False
    if P == u and Q >= v: return False
    return True
    
  for v in vv:
    if gcd(a-1,v-1) > 1: continue # No accepting state in this case
    for l in range(a):
      b = l*a - a**2
      rsols = solve_linear_congruence(v,b,u,bound=a)
      for r in rsols:
        t = (-b + r*v)//u
        br = (r,t)
        if not is_good_pair((u,v),br): continue
        b0 = (a*r,a*t+l-a)
        if not is_good_pair((u,v-a),b0): continue        
        v_vals[v].append((br,b0,l,r))
  return dict(v_vals)  

#################################  UTILITIES  ##################################

def construct_automata(base, trim=True):
  r"""
  Return a list of all nontrivial RSPAutomaton objects for given base

  INPUT:

  - ``base`` -- an integer > 1

  - ``trim`` -- bool (default: True); whether to trim the resulting DFA

  OUTPUT:

  - A list of RSPAutomaton objects for given base that consist of more than just
    the initial state. Output is sorted according to increasing value of a. 

  EXAMPLES::

    >>> for A in construct_automata(10):
    ...   print(A)
    ...
    RSPAutomaton with base = 10 and a = 2
      States: 3
      Transitions: 4
      Accepting: 2
      Trimmed: True
    <BLANKLINE>
    RSPAutomaton with base = 10 and a = 3
      States: 2
      Transitions: 1
      Accepting: 1
      Trimmed: True
    <BLANKLINE>
    RSPAutomaton with base = 10 and a = 9
      States: 2
      Transitions: 1
      Accepting: 1
      Trimmed: True
    <BLANKLINE>

  """
  automata = []
  for a in range(2,base):
    A = RSPAutomaton(base,a)
    if trim: A.trim()
    if A.num_states() > 1: automata.append(A)
  return automata

#################################  UTILITIES  ##################################

def construct_generic_automata(a, trim=True, name='T'):
  r"""
  Return a list of all nontrivial RSPGenericAutomaton objects for given a

  INPUT:

  - ``a`` -- a positive int

  - ``trim`` -- bool (default: True); whether to trim the resulting DFA

  - ``name`` -- str (default: 'T'); to be used for printing the affine parameter

  OUTPUT:

  - A list of RSPGenericAutomaton objects for given value of `a` that consist of
    more than just the initial state. Output is sorted according to increasing
    value of residue of `base (mod a^2 - 1)`.

  EXAMPLES::

    >>> for A in construct_generic_automata(2):
    ...   print(A)
    ...
    RSPGenericAutomaton with base = 3T and a = 2
      States: 2
      Transitions: 1
      Accepting: 1
      Trimmed: True
    <BLANKLINE>
    RSPGenericAutomaton with base = 3T + 1 and a = 2
      States: 3
      Transitions: 4
      Accepting: 2
      Trimmed: True
    <BLANKLINE>
    RSPGenericAutomaton with base = 3T + 2 and a = 2
      States: 2
      Transitions: 1
      Accepting: 1
      Trimmed: True
    <BLANKLINE>

    >>> for A in construct_generic_automata(4):
    ...   print(A)
    ...
    RSPGenericAutomaton with base = 15T + 3 and a = 4
      States: 2
      Transitions: 1
      Accepting: 1
      Trimmed: True
    <BLANKLINE>
    RSPGenericAutomaton with base = 15T + 6 and a = 4
      States: 5
      Transitions: 5
      Accepting: 2
      Trimmed: True
    <BLANKLINE>
    RSPGenericAutomaton with base = 15T + 9 and a = 4
      States: 8
      Transitions: 9
      Accepting: 1
      Trimmed: True
    <BLANKLINE>
    RSPGenericAutomaton with base = 15T + 11 and a = 4
      States: 2
      Transitions: 1
      Accepting: 1
      Trimmed: True
    <BLANKLINE>

  """
  automata = []
  modulus = a**2 - 1
  for v in range(modulus):
    A = RSPGenericAutomaton(a,v,name=name)
    if trim: A.trim()
    if A.num_states() > 1: automata.append(A)
  return automata

################################################################################
##################################  RSPChar  ###################################
################################################################################

class RSPChar():
  r"""
  Class for printing elements of the reversed sum-product DFA alphabet

  INPUT:

  - ``base`` -- an integer > 1

  - ``char`` -- a 1-tuple or 2-tuple of ints in the range `[0,base)`
  
  """
  def __init__(self, base, char):
    self._base = base
    self._char = char

  def __repr__(self):
    s = 'RSPChar({}, {})'
    return s.format(self._base,self._char)

  def __str__(self):
    base = self._base
    char = self._char
    if len(char) == 1:
      s = '({})'
    else:
      s = '({}, {})'
    if base > 62:
      args = char
    else:
      args = [string_format(base,(u,)) for u in char]
    return s.format(*args)

  def char(self):
    return self._char

  def len(self):
    return len(self._char)

# End RSPChar

################################################################################
##################################  RSPState  ##################################
################################################################################

class RSPState():
  r"""
  Class for handling the data of a reversed sum-product DFA state

  INPUT:

  - ``base`` -- an integer > 1

  - ``a`` -- an int in the range [1,base)

  - ``l_or_kind`` -- an int in the range `[0, a)` or a string among either
    'initial' or 'odd'

  - ``r`` -- int in the range `[0,a)` (default: None); must be specified 
    if ``l_or_kind`` is an int

  NOTES:

  - If ``l_or_kind`` is not 'initial' or 'odd', then this is a carry state
    as in [1], Section 5.3

  - For purposes of comparison, the ordering on RSPStates is:

    initial state < carry states < odd state

    and the carry states are ordered by the value of tuple().

  """
  def __init__(self, base, a, l_or_kind, r=None):
    if isinstance(l_or_kind,str):
      if l_or_kind == 'initial':
        kind = 'initial'
        accepting = False
      elif l_or_kind == 'odd':
        kind = 'odd'
        accepting = True
      else:
        msg = "Argument l_or_kind = {} must be an int or 'initial' or 'odd'"
        raise ValuError(msg.format(l_or_kind))
      l = None
      r = None
    else:
      if r is None:
        msg = 'Must specify r when l_or_kind argument is an int'
        raise ValueError(msg)
      l = l_or_kind
      kind = 'carry'
      accepting = (l == r)

    self._base = base
    self._a = a      
    self._l = l
    self._r = r
    self._kind = kind
    self._accepting = accepting

  ################################  RSPState  ##################################    

  def base(self):
    return self._base

  def a(self):
    return self._a
  
  def l(self):
    return self._l

  def r(self):
    return self._r

  def tuple(self):
    if self.is_carry():
      t = (self._base, self._a, self._l, self._r)
    else:
      t = (self._base, self._a, self._kind)
    return t

  def kind(self):
    return self._kind

  ################################  RSPState  ##################################

  def is_carry(self):
    return self._kind == 'carry'

  def is_odd(self):
    return self._kind == 'odd'

  def is_initial(self):
    return self._kind == 'initial'

  def is_accepting(self):
    return self._accepting
  
  ################################  RSPState  ##################################  
  
  def __repr__(self):
    if self.is_carry():
      s = 'RSPState({}, {}, {}, {})'
    else:
      s = "RSPState({}, {}, '{}')"
    return s.format(*self.tuple())

  def __str__(self):
    if self.is_initial():
      return 'i'    
    if self.is_odd():
      return 'o'
    # A carry state
    base = self._base
    if base > 62:
      return str(self.tuple()[2:])
    s = '({}, {})'
    reps = [string_format(base,(u,)) for u in self.tuple()[2:]]
    return s.format(*reps)
  
  def __hash__(self):
    return hash(self.tuple())

  def __eq__(self, other):
    if not isinstance(other,RSPState):
      return False
    return self.tuple() == other.tuple()

  def __ne__(self, other):
    return not self.__eq__(other)  

  def __lt__(self, other):
    if not isinstance(other,RSPState): raise ValueError
    if self.__eq__(other): return False
    if self.is_initial(): return True
    if other.is_initial(): return False
    if self.is_odd(): return False
    if other.is_odd(): return True
    # self and other are carry states now
    return self.tuple() < other.tuple()

  def __gt__(self, other):
    if not isinstance(other,RSPState): raise ValueError
    if self.__eq__(other): return False
    return not self.__lt__(other)

  def copy(self):
    return RSPState(*self.tuple())

  ################################  RSPState  ##################################  

  def out_states(self):
    r"""
    Return all target states for the DFA defined in [1], Section 5.3

    OUTPUT:

    - A dict whose keys are the RSPState objects that are out nodes for the DFA
      graph, and whose values are RSPChar objects (for edge labels)

    NOTE:

    - A given out state cannot have more than one transition from self to
      it. See the notes at the top of this file.

    """
    if self.is_odd():
      return {}
    
    base = self._base
    a = self._a
    outs = {}
    if self.is_initial():
      starts = recursion_start(base,a).get(a,[])
      for (br,b0,l,r) in starts:
        q = RSPState(base,a,l,r)
        label = RSPChar(base,(br,b0))
        outs[q] = label
      if self.is_initial() and a in [2,base-1]:
        qo = RSPState(base,a,'odd')
        label = RSPChar(base,(a,))
        if a == 2 and base >= 5:
          outs[qo] = label
        if a == base-1 and base >= 3:
          outs[qo] = label
      return outs

    # self is a carry state
    l = self._l
    r = self._r
    g = gcd(a**2 - 1, base)
    qo = RSPState(base,a,'odd')
    next_ls = solve_linear_congruence(1,-a*r,g,bound=a)
    for next_l in next_ls:
      next_ys = solve_linear_congruence(a**2 - 1, -a*r - next_l,base)
      for next_y in next_ys:
        next_x = (a*next_y + r) % base
        if a*next_x + next_l != next_y + l*base: continue
        next_r = (a*next_y + r - next_x) // base
        args = (base, a, next_l, next_r)
        q = RSPState(*args)
        label = RSPChar(base,(next_x, next_y))
        outs[q] = label
        if next_x == next_y:
          label = RSPChar(base,(next_x,))
          outs[qo] = label
    return dict(outs)

# End RSPState


################################################################################
################################  RSPAutomaton  ################################
################################################################################

class RSPAutomaton():
  r"""
  Class for constructing and manipulating a reversed sum-product DFA

  INPUT:

  - Exactly one of the following sets of keyword arguments must be specified:

    * ``base`` -- an integer > 1

    * ``a`` -- an int in the interval `(0,base)`

    or 

    * ``states`` -- a list of RSPState objects 

    * ``transitions`` -- a dict whose keys are pairs of elements of ``states``
      and whose values are RSPChar objects

  NOTES:

  - All states `q` in ``states`` must have the same value of q.a() and q.base()

  """
  def __init__(self, base=None, a=None, states=None, transitions=None):
    
    # If base, a are specified, we run the graph construction algorithm.
    # Otherwise, we check that base, a are well-defined. 
    if None not in [base,a]:
      states, transitions = self._construct_dfa(base,a)
    elif None not in [states, transitions]:
      a_vals = set(q.a() for q in states)
      if len(a_vals) != 1:
        raise ValueError('Unable to determine a from states: {}'.format(a_vals))
      base_vals = set(q.base() for q in states)
      if len(base_vals) != 1:
        raise ValueError('Unable to determine base from states: {}'.format(base_vals))
      for (q1,q2),t in transitions.items():
        if q1 not in states or q2 not in states:
          s = 'Transition ({},{}) does not connect known states'
          raise ValueError(s.format(q1,q2))
      a = a_vals.pop()
      base = base_vals.pop()
    else:
      msg = 'Must specify either `base` and `a` or `states` and `transitions`'
      raise ValueError(msg)
        
    self._a = a
    self._base = base
    self._states = states
    self._transitions = transitions
    self._outs = None
    self._initial = None
    self._odd = None
    self._accepting_states = None
    self._trimmed = False

  ##############################  RSPAutomaton  ################################
  
  def __repr__(self):
    base = self._base
    a = self._a
    return 'RSPAutomaton({},{})'.format(base,a)
    
  def __str__(self):
    base = self._base
    a = self._a
    a_rep = string_format(base,(a,))
    s = 'RSPAutomaton with base = {} and a = {}\n'
    s = s.format(base,a_rep)
    s += '  States: {}\n'.format(self.num_states())
    s += '  Transitions: {}\n'.format(self.num_transitions())
    s += '  Accepting: {}\n'.format(self.num_accepting_states())
    s += '  Trimmed: {}\n'.format(self.is_trimmed())
    return s  

  ##############################  RSPAutomaton  ################################
  
  def _construct_dfa(self, base, a):
    r"""
    Run the recursion that constructs the DFA
    """
    # Begin with only the initial state
    qi = RSPState(base,a,'initial')
    transitions = {}
    frontier = [qi]
    seen_states = set(frontier)
    while frontier != []:
      q = frontier.pop(0) 
      for next_q,t in q.out_states().items():
        edge = (q, next_q)
        transitions[edge] = t        
        if next_q in seen_states:
          # completed a cycle
          continue
        seen_states.add(next_q)
        frontier.append(next_q)
    return list(seen_states),transitions  

  ##############################  RSPAutomaton  ################################

  def base(self):
    return self._base

  def a(self):
    return self._a

  def is_trimmed(self):
    return self._trimmed

  ##############################  RSPAutomaton  ################################

  def states(self):
    r"""
    Return a list of copies of the states of self
    """
    return [q.copy() for q in self._states]

  def transitions(self):
    r"""
    Return a copy of the dict of transitions
    """
    D = {}
    for (q1,q2),t in self._transitions.items():
      D[(q1.copy(),q2.copy())] = t
    return D

  def transition(self, p, q):
    r"""
    Return the label on the transition p -> q, or None if no such exists
    """
    return self._transitions.get((p,q))

  def accepting_states(self):
    r"""
    Cache and return the list of accepting states
    """
    accepting = self._accepting_states
    if accepting is not None:
      return accepting
    accepting = [q for q in self._states if q.is_accepting()]
    accepting.sort()
    self._accepting_states = accepting
    return accepting

  def initial_state(self):
    r""" 
    Cache and return the initial state
    """
    qi = self._initial
    if qi is not None:
      return qi
    for q in self._states:
      if q.is_initial():
        qi = q
        break
    self._initial = qi
    return qi

  def odd_state(self):
    r"""
    Cache and return the odd state, if it exists
    """
    qodd = self._odd
    if qodd is not None:
      return qodd
    for q in self._states:
      if q.is_odd():
        qodd = q
        break
    self._odd = qodd
    return qodd
    
  def out_states(self, q):
    r"""
    Cache and return the list of outward states from q
    """
    outs = self._outs
    if outs is not None:
      return outs[q]
    self._outs = outs = {q:[] for q in self._states}
    for q1,q2 in self._transitions:
      outs[q1].append(q2)
    return outs[q]

  ##############################  RSPAutomaton  ################################

  def __eq__(self, other):
    r"""
    EXAMPLES::

      >>> A = RSPAutomaton(18,11)
      >>> B = RSPAutomaton(18,11)
      >>> B.trim()
      >>> A == B
      False
      >>> A.trim()
      >>> A == B
      True

    """
    if not isinstance(other,RSPAutomaton): return False
    if self.a() != other.a(): return False
    if self.base() != other.base(): return False
    Astates = sorted(self.states())
    Bstates = sorted(other.states())
    if len(Astates) != len(Bstates): return False
    for qA,qB in zip(Astates,Bstates):
      if qA.tuple() != qB.tuple(): return False
    Aedges = self.transitions()
    Bedges = other.transitions()
    if len(Aedges) != len(Bedges): return False
    for (q1,q2),char in Aedges.items():
      if (q1,q2) not in Bedges: return False
      if char.char() != Bedges[(q1,q2)].char(): return False
    return True

  def __ne__(self, other):
    return not self.__eq__(other)

  ##############################  RSPAutomaton  ################################  

  def num_states(self):
    return len(self._states)

  def num_transitions(self):
    return len(self._transitions)

  def num_accepting_states(self):
    return len(self.accepting_states())

  ##############################  RSPAutomaton  ################################

  def trim(self):
    r"""
    Return a trimmed verison of self
    """
    if self._trimmed:
      return

    accepting = self.accepting_states()
    if len(accepting) == 0:
      self._states = [self.initial_state()]
      self._transitions = {}
      self._outs = None
      self._initial = None
      self._odd = None
      self._accepting_states = None
      self._trimmed = True
      return

    # breadth-first search to determine states with no accessible accepting
    # state. Initial state will be a good state since the accepting set is
    # nonempty.
    bad_states = set()
    initial = self.initial_state()
    Q = self._states
    for q in Q:
      if q == self.initial_state(): continue
      frontier = [q]
      visited = set()
      while frontier != []:
        p = frontier.pop()
        if p in accepting:
          visited = set()
          break
        if p in visited:
          continue
        visited.add(p)
        for r in self.out_states(p):
          frontier.append(r)
      bad_states.update(visited)

    Q_new = [q for q in Q if q not in bad_states]
    Qset = set(Q_new)
    T_new = {}
    for (p,q),t in self._transitions.items():
      if p in Qset and q in Qset:
        T_new[(p,q)] = t
    self._states = Q_new
    self._transitions = T_new
    self._outs = None
    self._initial = initial
    self._odd = None
    self._accepting_states = None
    self._trimmed = True

  ##############################  RSPAutomaton  ################################
  
  def b_values(self, bound):
    r"""
    Return the list of `b` such that (self.a(), b) are a reversed sum-product pair

    INPUT:

    - ``bound`` -- a positive integer

    OUTPUT:

    - A sorted list of all values `b` in given base such that 

      * (self._a, b) is a reversed sum-product pair for base self._base, and

      * `b` has at at most ``bound`` digits.

    EXAMPLES::

      >>> A = RSPAutomaton(10,2)
      >>> A.b_values(5)
      ['2', '47', '497', '4997', '49997']

      >>> A = RSPAutomaton(18,7)
      >>> A.b_values(12)
      ['2483D8', '2483D9E483D8']

    """
    if bound < 1: return []
    base = self._base
    src = self.initial_state()
    accepting = self.accepting_states()
    frontier = [(src,(),())]
    b_values = []    
    
    while bound > 0:
      new_frontier = []    
      while frontier != []:
        p, first, last = frontier.pop()
        for q in self.out_states(p):
          t = self.transition(p,q)
          if q.is_accepting() and bound >= len(t.char()):
            b = string_format(base,first + t.char() + last)
            b_values.append(b)          
          if t.len() == 1:
            assert q == self.odd_state()
            continue
          # t = (x,y) now
          x,y = t.char()
          new_frontier.append((q, first + (x,), (y,) + last))
      frontier = new_frontier
      bound -= 2
    b_values.sort(key=lambda s : (len(s),s))
    return b_values

  ##############################  RSPAutomaton  ################################

  def regex(self):
    r"""
    Return a regular expression that gives the same language as self

    OUTPUT:

    - A string representing a regular expression or 'EMPTY' to denote the empty
      expression. Some basic simplification is performed if self.base() < 62

    NOTES:

    - Square brackets are used interchangeably with parentheses in the string
      output. This is because transitions in the RSPAutomaton include
      parenthetic expressions as part of the alphabet. 

    - We are following the state-elimination procedure described in 3.2.2
      of 

        Hopcroft, Motwani, Ullman. "Introduction to Automata Theory, 
        Languages, and Computation."3rd ed., Pearson, (2007)

    EXAMPLES::

      >>> A = RSPAutomaton(10, 4)
      >>> A.regex()
      'EMPTY'

      >>> A = RSPAutomaton(10,2)
      >>> A.regex()
      '(4, 7)(9, 9)* + [(2) + (4, 7)(9, 9)*(9)]'

      >>> A = RSPAutomaton(18,7)
      >>> A.regex()
      '(248, 3D8)(3D9E48, 3D9E48)* + (2483D9, E483D8)(E483D9, E483D9)*'
      
      >>> A = RSPAutomaton(17, 6)
      >>> A.regex()
      '(1A3)'
      >>> is_rsp_pair(17,'6','1A3')
      True

    """
    if self.num_accepting_states() == 0:
      return 'EMPTY'
    self.trim()

    # Set up the minimum amount of data for the state-collapsing procedure. At
    # initialization, at most one transition between any two states exists
    # (including loops).
    edges = defaultdict(lambda:'')
    for (p,q),t in self._transitions.items():
      edges[(p,q)] = str(t)

    # Collapse all non-accepting states
    verts = self.states() # a copy
    verts.sort() # To ensure output is the same every time. 
    while len(verts) > 0:
      s = verts.pop()
      if s.is_initial(): continue
      if s.is_accepting(): continue
      S = edges[(s,s)]
      remove_edges = [(s,s)]
      ins  = [a for a,b in edges if b == s and a != s]
      outs = [b for a,b in edges if a == s and b != s]
      for q in ins:
        remove_edges.append((q,s))
      for p in outs:
        remove_edges.append((s,p))
      for q,p in product(ins,outs):
        Q = edges[(q,s)]
        P = edges[(s,p)]
        if S == '':
          new_expr = Q + P
        else:
          new_expr = Q + '[' + S + ']*' + P
        old_expr = edges[(q,p)]
        if old_expr == '':
          edges[(q,p)] = new_expr
        else:
          edges[(q,p)] = '[' + old_expr + ' + ' + new_expr + ']'
      for q,p in remove_edges:
        del edges[(q,p)]

    # for each accepting state, run the contraction
    # procedure again and report the result.
    regex = ''
    for qq in self.accepting_states():
      qq_edges = edges.copy()
      verts = self.accepting_states()[:] # a copy
      while len(verts) > 0:
        s = verts.pop()
        if s == qq: continue        
        S = qq_edges[(s,s)]
        remove_edges = [(s,s)]
        ins  = [a for a,b in qq_edges if b == s and a != s]
        outs = [b for a,b in qq_edges if a == s and b != s]
        for q in ins:
          remove_edges.append((q,s))
        for p in outs:
          remove_edges.append((s,p))        
        for q,p in product(ins,outs):
          Q = qq_edges[(q,s)]
          P = qq_edges[(s,p)]
          if S == '':
            new_expr = Q + P
          else:
            new_expr = Q + '[' + S + ']*' + P
          old_expr = qq_edges[(q,p)]
          if old_expr == '':
            qq_edges[(q,p)] = new_expr
          else:
            qq_edges[(q,p)] = old_expr + ' + ' + new_expr
        for q,p in remove_edges:
          del qq_edges[(q,p)]
      qq_edges_list = list(qq_edges.keys())
      qi = self.initial_state()
      # Graph should now be an edge from q_i to qq and possibly a loop at qq
      if qq_edges_list not in [[(qi,qq)], [(qi,qq),(qq,qq)], [(qq,qq),(qi,qq)]]:
        msg = 'Unexpected form after eliminating all but state {}\n'
        msg += '  Edges: {}'
        raise RuntimeError(msg.format(qq,dict(qq_edges)))
      S = qq_edges[(qi,qq)]
      U = qq_edges[(qq,qq)]
      new_expr = '[' + S + ']'
      if U != '':
        new_expr += '[' + U + ']*'
      if regex == '':
        regex = new_expr
      else:
        regex += ' + ' + new_expr

    if self.base() >= 62: return regex
    
    # Concatenate adjacent edge labels: e.g., (2, 8)(4, D) -> (24, D8)
    pattern = r'(\([0-9a-zA-Z]+, [0-9a-zA-Z]+\)){2,}'
    match = search(pattern,regex)
    while match is not None:
      pairs = match.group()[1:-1].split(')(') # Divide into pairs, without parens
      first, last = '', ''
      for pair in pairs:
        a,b = pair.split(',')
        b = b.strip()
        first = first + a
        last  = b + last
      start, finish = match.span()
      regex = regex[:start] + '(' + first + ', ' + last + ')' + regex[finish:]
      match = search(pattern,regex)

    # Concatenate adjacent edge labels where one is a singleton: e.g., (1, 3)(A) -> (1A3)
    pattern = r'\([0-9a-zA-Z]+, [0-9a-zA-Z]+\)\([0-9a-zA-Z]+\)'
    match = search(pattern,regex)
    while match is not None:
      pair, single = match.group()[1:-1].split(')(') # Divide into ['1, 3', 'A']
      first, last = pair.split(',')
      last = last.strip()
      new = first + single + last
      start, finish = match.span()
      regex = regex[:start] + '(' + new + ')' + regex[finish:]
      match = search(pattern,regex)
    

    # Remove superfluous brackets
    pattern1 = r'\[\([0-9a-zA-Z]+, [0-9a-zA-Z]+\)\]'  # e.g., [(4, 7)]
    pattern2 = r'\[\([0-9a-zA-Z]+\)\]'                # e.g., [(9)]
    pattern = pattern1 + '|' + pattern2
    match = search(pattern,regex)
    while match is not None:
      start, finish = match.span()
      new = match.group()[1:-1] # remove the brackets
      regex = regex[:start] + new + regex[finish:]
      match = search(pattern,regex)      
    return regex

  ##############################  RSPAutomaton  ################################

  def sage_graph(self):
    r"""
    Return a Sage DiGraph object (if available)
    """
    try:
      from sage.graphs.digraph import DiGraph
    except ModuleNotFoundError:
      raise ModuleNotFoundError('Functionality only available in Sage')
    data = {}
    Ts = self._transitions
    for q1 in self._states:
      data[q1] = {q2:Ts[(q1,q2)] for q2 in self.out_states(q1)}
    return DiGraph(data,loops=True)

  ##############################  RSPAutomaton  ################################

  def sage_plot(self, color1='palegoldenrod', color2='lightblue', 
                color3='palevioletred', vertex_labels=False, edge_labels=True, **kwargs):
    r"""
    Return a plot object using Sage (if available)

    INPUT:

    - ``color1, color2, color3`` -- strings recognized by MatPlotLib as colors

    - ``vertex_labels`` -- bool (default: False); whether to print vertex labels

    - ``edge_labels`` -- bool (default: True); whether to print edge labels

    - Additional keywords are passed to the plot() method.      

    OUTPUT:

    - A Sage plot object of self, with color1 indicating the initial state, 
      color2 indicating an accepting state, and color3 indicating a 
      non-accepting non-initial state

    NOTES:

    - To display this object in Sage, use the show() function.

    - Try plotting the same object several times; there is randomness in how Sage
      chooses the locations for the states.

    """
    verts1 = [self.initial_state()]
    verts2 = self.accepting_states()
    verts3 = [q for q in self._states if q not in verts1+verts2]
    vert_colors = {color1:verts1, color2:verts2, color3:verts3}

    G = self.sage_graph()
    base = self._base
    a_rep = string_format(base,(self._a,))
    title = 'base = {}, a = {}'.format(base,a_rep,)
      
    kwds = {}
    kwds['title'] = title
    kwds['vertex_colors'] = vert_colors
    kwds['vertex_labels'] = vertex_labels
    kwds['talk'] = vertex_labels # Use large vertices if vertex_labels is True
    kwds['edge_labels'] = edge_labels
    for key,val in kwargs.items():
      kwds[key] = val
    return G.plot(**kwds)

  ##############################  RSPAutomaton  ################################
  
  def sage_automaton(self):
    r"""
    Return the Sage Automaton object (if available)

    OUTPUT:

    - A Sage Automaton object with the same states and transitions at self.

    """
    try:
      from sage.combinat.finite_state_machine import Automaton
    except ModuleNotFoundError:
      raise ModuleNotFoundError('Functionality only available in Sage')
      
    self.trim()

    # Index the states
    states = self.states()
    final = []
    states.sort()
    assert states[0].is_initial()
    new_states = {}
    for q in states:
      ind = len(new_states)
      new_states[q] = ind
      if q.is_accepting():
        final.append(ind)

    trans = []
    for (p,q),t in self._transitions.items():
      label = str(t)
      trans.append( (new_states[p], new_states[q], label) )    

    kwargs = {}
    kwargs['initial_states'] = [0]
    kwargs['final_states'] = final
    return Automaton(trans,**kwargs)

  ##############################  RSPAutomaton  ################################

  def graphviz_graph(self):
    r"""
    Return a pygraphviz.AGraph object (if available)
    """
    try:
      from pygraphviz import AGraph
    except ModuleNotFoundError:
      msg = 'Functionality only available if pygraphviz is installed'
      raise ModuleNotFoundError(msg)

    G = AGraph(directed=True)
    for (q1,q2),label in self._transitions.items():
      G.add_edge(q1,q2,label=label)
    return G

  ##############################  RSPAutomaton  ################################  

  def graphviz_draw(self, filename=None, layout='dot', node_labels=False,
                    node_attributes=None, edge_labels=True, edge_attributes=None,
                    graph_attributes=None, colors=('khaki','lightblue','lightpink')):
    r"""
    Return a pygraphviz.AGraph object

    INPUT:

    - ``filename`` -- optional string to use for file to write output; extension
      will determine the file format. Typical choices are 'jpeg', 'jpg', 'png',
      'svg', 'ps','pdf','fig','dot', though there are many others.

    - ``layout`` -- string (default: 'dot'); layout style to use for drawing; 
      options are 'neato', 'dot', 'twopi', 'circo', or 'fdp'

    - ``node_labels`` -- bool (default: False); whether to print node labels

    - ``node_attributes`` -- optional dict whose keys are states of self and
      and whose values are dicts of additional attributes to be set for the
      associated pygraphviz.AGraph node objects

    - ``edge_labels`` -- bool (default: True); whether to print edge labels

    - ``edge_attributes`` -- optional dict whose keys are pairs of states of
      self and and whose values are dicts of additional attributes to be set for
      the associated pygraphviz.AGraph edge objects

    - ``graph_attributes`` -- optional dict of attributes to pass to the 
      pygraphviz.AGraph object; by default, only the directed attribute and 
      the label attribute are set

    - ``colors`` -- a triple of strings recognized by graphviz as colors

    OUTPUT:

    - A pygraphviz.AGraph object with all specified attributes set

    EFFECT:

    - Construct a pygraphviz.AGraph object and call its draw method, writing the
      output to ``filename``. If the colors specified are
      `(color1,color2,color3)`, then color1 is used for the initial state,
      color2 is used for the accepting states, and color3 is used for
      non-accepting non-initial states.

    BUG:

    - For some reason, when node_labels is set to True, one or more of the node
      labels is randomly set to None.

    """
    node_shape = 'oval' if node_labels else 'circle'
    node_label = lambda s : s if node_labels else ''
    edge_label = lambda s : s if edge_labels else ''    
    init_color,acc_color,gen_color = colors
    base = self._base
    a_rep = string_format(base,(self._a,))
    title = 'base = {}, a = {}'.format(base,a_rep,)
    if node_attributes is None: node_attributes = {}
    if edge_attributes is None: edge_attributes = {}
    if graph_attributes is None: graph_attributes = {}
    if 'label' not in graph_attributes:
      graph_attributes['label'] = title
    
    G = self.graphviz_graph()
    for attr,val in graph_attributes.items():
      G.graph_attr[attr] = val
    G.layout(prog=layout)
    
    for q in self._states:
      n = G.get_node(q)
      label = n.attr['label']
      n.attr['shape'] = node_shape
      n.attr['style'] = 'filled'
      n.attr['label'] = node_label(label)
      if node_shape == 'circle':
        n.attr['height'] = 0.25
        n.attr['width']  = 0.25
      if q.is_initial():
        n.attr['fillcolor'] = init_color
      elif q.is_accepting():
        n.attr['fillcolor'] = acc_color
      else:
        n.attr['fillcolor'] = gen_color
      q_attrs = node_attributes.get(q)
      if q_attrs is None: continue
      for attr,val in q_attrs.items():
        n.attr[attr] = val
      
    for (q1,q2) in self._transitions:
      e = G.get_edge(q1,q2)
      label = e.attr['label']
      e.attr['label'] = edge_label(label)
      e_attrs = edge_attributes.get((q1,q2))
      if e_attrs is None: continue
      for attr,val in e_attrs.items():
        e.attr[attr] = val
    if filename is not None:
      G.draw(filename)
    return G

# End RSPAutomaton
    
################################################################################
###############################  RSPGenericChar  ###############################
################################################################################

class RSPGenericChar():
  r"""
  Class for printing elements of the generic reversed sum-product DFA alphabet

  INPUT:

  - ``base`` -- a pair of ints `(u,v)`, corresponding to the generic base 
    `uT + v` with `T` a parameter

  - ``char`` -- a 1-tuple or 2-tuple of pairs of ints `(r,s)` with the property 
    that `rT + s < uT + v` for `T` sufficiently large. 

  - ``name`` -- str (default: 'T'); to be used for printing the affine 
    parameter
  
  """
  def __init__(self, base, char, name='T'):
    u,v = base
    for r,s in char:
      if r > u or r < 0:
        raise ValueError('Invalid element of the generic alphabet: base = {}, char = {}'.format(base,char))
      if r == u and v < s:
        raise ValueError('Invalid element of the generic alphabet: base = {}, char = {}'.format(base,char))
    self._base = base
    self._char = char
    self._name = name

  #############################  RSPGenericChar  ###############################

  def char(self):
    return self._char

  def len(self):
    return len(self._char)

  def __repr__(self):
    s = 'RSPGenericChar({}, {})'
    return s.format(self._base,self._char)

  def __str__(self):
    u,v = self._base
    char = self._char
    name = self._name
    strings = [generic_string(pair,name) for pair in char]
    if len(char) == 1:
      s = '({})'.format(*strings)
    else:
      s = '({}, {})'.format(*strings)
    return s

  #############################  RSPGenericChar  ###############################
  
  def __call__(self, t):
    r"""
    Return the specialization of self at the parameter t

    INPUT:

    - ``t`` -- a positive integer

    OUTPUT:

    - An RSPChar object given by evaluating self._base at `T = t`. If this does
      not yield a valid RSPChar because `t` is too small, then None is
      returned.

    """
    u,v = self._base
    base = u*t + v
    if base < 2: return None

    chars = tuple(u*t + v for u,v in self._char)
    if all(0 <= char < base for char in chars):
      return RSPChar(base,chars)
    return None
  
# End RSPGenericChar

################################################################################
###############################  RSPGenericState  ##############################
################################################################################

class RSPGenericState():
  r"""
  Class for handling the data of a generic reversed sum-product DFA state

  INPUT:

  - ``base`` -- a pair of ints `(u,v)`, corresponding to the generic base 
    `uT + v` with `T` a parameter

  - ``a`` -- a positive int

  - ``l_or_kind`` -- an int in the range `[0, a)` or a string among either
    'initial' or 'odd'

  - ``r`` -- int in the range `[0,a)` (default: None); must be specified if
    ``l_or_kind`` is an int

  - ``name`` -- str (default: 'T'); to be used for printing the affine parameter

  NOTES:

  - If ``l_or_kind`` is not 'initial' or 'odd', then this is a carry state
    as in [1], Section 5.3

  - For purposes of comparison, the ordering on RSPGenericStates is:

    initial state < carry states < odd state

    and the carry states are ordered by the value of tuple().

  """
  def __init__(self, base, a, l_or_kind, r=None, name='T'):
    if isinstance(l_or_kind,str):
      if l_or_kind == 'initial':
        kind = 'initial'
        accepting = False
      elif l_or_kind == 'odd':
        kind = 'odd'
        accepting = True
      else:
        msg = "Argument l_or_kind = {} must be an int or 'initial' or 'odd'"
        raise ValuError(msg.format(l_or_kind))
      l = None
      r = None
    else:
      if r is None:
        msg = 'Must specify r when l_or_kind argument is an int'
        raise ValueError(msg)
      l = l_or_kind
      kind = 'carry'
      accepting = (l == r)

    self._base = base
    self._a = a      
    self._l = l
    self._r = r
    self._name = name
    self._kind = kind
    self._accepting = accepting

  #############################  RSPGenericState  ##############################

  def base(self):
    return self._base

  def a(self):
    return self._a
  
  def l(self):
    return self._l

  def r(self):
    return self._r

  def tuple(self):
    if self.is_carry():
      t = (self._base, self._a, self._l, self._r)
    else:
      t = (self._base, self._a, self._kind)
    return t

  def kind(self):
    return self._kind
  
  #############################  RSPGenericState  ##############################

  def is_carry(self):
    return self._kind == 'carry'

  def is_odd(self):
    return self._kind == 'odd'

  def is_initial(self):
    return self._kind == 'initial'

  def is_accepting(self):
    return self._accepting

  #############################  RSPGenericState  ##############################  
  
  def __repr__(self):
    if self.is_carry():
      s = 'RSPGenericState({}, {}, {}, {})'
    else:
      s = "RSPGenericState({}, {}, '{}')"
    return s.format(*self.tuple())

  def __str__(self):
    if self.is_initial():
      return 'i'    
    if self.is_odd():
      return 'o'
    # A carry state
    s = '({}, {})'
    return s.format(self._l, self._r)
  
  def __hash__(self):
    return hash(self.tuple())

  def __eq__(self, other):
    if not isinstance(other,RSPGenericState):
      return False
    return self.tuple() == other.tuple()

  def __ne__(self, other):
    return not self.__eq__(other)  

  def __lt__(self, other):
    if not isinstance(other,RSPGenericState): raise ValueError
    if self.__eq__(other): return False
    if self.is_initial(): return True
    if other.is_initial(): return False
    if self.is_odd(): return False
    if other.is_odd(): return True
    # self and other are carry states now
    return self.tuple() < other.tuple()

  def __gt__(self, other):
    if not isinstance(other,RSPGenericState): raise ValueError
    if self.__eq__(other): return False
    return not self.__lt__(other)

  def copy(self):
    return RSPGenericState(*self.tuple(),name=self._name)

  def __call__(self, t):
    r"""
    Return the specialization of self at the parameter t

    INPUT:

    - ``t`` -- a positive integer

    OUTPUT:

    - An RSPState object given by evaluating self._base at `T = t`. If this does
      not yield a valid RSPState because `t` is too small, then None is
      returned.

    """
    a = self._a
    u,v = self._base
    base = u*t + v
    if base < 2: return None
    
    if self.is_odd():
      args = (base,a,'odd')
    elif self.is_initial():
      args = (base,a,'initial')
    else:
      # carry state case
      l,r = self._l, self._r
      args = (base,a,l,r)
    return RSPState(*args)

  #############################  RSPGenericState  ##############################

  def out_states(self):
    r"""
    Return all target states for the DFA defined as in [1], Section 5.3

    OUTPUT:

    - A dict whose keys are the RSPGenericState objects that are out nodes for
      the DFA graph, and whose values are RSPGenericChar objects (for edge
      labels)

    NOTES:

    - A given out state cannot have more than one transition from self to
      it. See the notes at the top of this file.

    - Solutions are generic in the sense that they are valid for all
      sufficiently large parameter values `T`. It is possible for a proper
      subset of the solutions to be valid for smaller values of `T`.

    """
    if self.is_odd():
      return {}
    
    base = self._base
    _,v = base
    a = self._a
    outs = {}
    if self.is_initial():
      starts = generic_recursion_start(a,v).get(v,[])
      for (br,b0,l,r) in starts:
        q = RSPGenericState(base,a,l,r)
        label = RSPGenericChar(base,(br,b0))
        outs[q] = label
      if self.is_initial() and a == 2:
        qo = RSPGenericState(base,2,'odd')
        label = RSPGenericChar(base,((0,2),))
        outs[qo] = label
      return outs

    # Insist that any solutions give rise to an infinite family of RSPAutomata
    def is_good_pair(base,pair):
      u,v = base
      P,Q = pair
      # PT + Q >= 0 for T >> 0
      if P < 0: return False
      if P == 0 and Q < 0: return False
      # PT + Q < uT + v for T >>0
      if P > u: return False
      if P == u and Q >= v: return False
      return True

    # self is a carry state
    l = self._l
    r = self._r
    u = a**2-1
    qo = RSPGenericState(base,a,'odd')
    for next_r in range(a):
      next_ls = solve_linear_congruence(a,next_r*v-r+a*l*v,u,bound=a)
      for next_l in next_ls:
        b = (next_r*v-r+a*l*v - a*next_l)//u
        next_x = (next_r + a*l,b)
        if not is_good_pair(base,next_x): continue
        next_y = (a*next_r + l,a*b + next_l - l*v)
        if not is_good_pair(base,next_y): continue        
        args = (base, a, next_l, next_r)
        q = RSPGenericState(*args)
        label = RSPGenericChar(base,(next_x, next_y))
        outs[q] = label
        if next_x == next_y:
          label = RSPGenericChar(base,(next_x,))
          outs[qo] = label
    return dict(outs)

# End RSPGenericState

################################################################################
#############################  RSPGenericAutomaton  ############################
################################################################################

class RSPGenericAutomaton():
  r"""
  Class for constructing and manipulating a generic reversed sum-product DFA

  INPUT:

  - Exactly one of the following sets of keyword arguments must be specified:

    * ``a`` -- an int > 1

    * ``base_residue`` -- an int `v`, corresponding to the generic base
      `(a^2-1)T + v` with `T` a parameter

    or 

    * ``states`` -- a list of RSPGenericState objects 

    * ``transitions`` -- a dict whose keys are pairs of elements of ``states``
      and whose values are RSPGenericChar objects

  - ``name`` -- str (default: 'T'); to be used for printing the affine parameter

  NOTES:

  - All states `q` in ``states`` must have the same value of q.a() and q.base()

  - These automata are generic in the sense that they give rise to isomorphic
    RSPAutomaton objects for all sufficiently large parameter values `T`. It is
    possible for a subset of the transitions to be valid for smaller values of
    `T`, but this object will not track such phenomena.

  """
  def __init__(self, a=None, base_residue=None,
               states=None, transitions=None, name='T'):
    
    # If a and base_residue are specified, we run the graph construction algorithm.
    # Otherwise, we check that a and base are well-defined. 
    if None not in [base_residue,a]:
      if a < 2:
        raise ValueError('Invalid a-value a = {}'.format(a))
      u = a**2 - 1
      v = base_residue % u
      base = (u,v)
      states, transitions = self._construct_generic_dfa(base,a,name)
    elif None not in [states, transitions]:
      a_vals = set(q.a() for q in states)
      if len(a_vals) != 1:
        raise ValueError('Unable to determine a from states: {}'.format(a_vals))
      base_vals = set(q.base() for q in states)
      if len(base_vals) != 1:
        raise ValueError('Unable to determine base from states: {}'.format(base_vals))
      for (q1,q2),t in transitions.items():
        if q1 not in states or q2 not in states:
          s = 'Transition ({},{}) does not connect known states'
          raise ValueError(s.format(q1,q2))
      a = a_vals.pop()
      base = base_vals.pop()
    else:
      msg = 'Must specify either `base` and `a` or `states` and `transitions`'
      raise ValueError(msg)
        
    self._a = a
    self._base = base
    self._name = name
    self._states = states
    self._transitions = transitions
    self._outs = None
    self._initial = None
    self._odd = None
    self._accepting_states = None
    self._min_spec = None
    self._trimmed = False

  ###########################  RSPGenericAutomaton  ############################
  
  def __repr__(self):
    _,v = self._base
    a = self._a
    return 'RSPGenericAutomaton({},{})'.format(a,v)
    
  def __str__(self):
    base = self._base
    a = self._a
    name = self._name
    base_rep = generic_string(base,name)
    s = 'RSPGenericAutomaton with base = {} and a = {}\n'
    s = s.format(base_rep,a)
    s += '  States: {}\n'.format(self.num_states())
    s += '  Transitions: {}\n'.format(self.num_transitions())
    s += '  Accepting: {}\n'.format(self.num_accepting_states())
    s += '  Trimmed: {}\n'.format(self.is_trimmed())
    return s
  
  ###########################  RSPGenericAutomaton  ############################
  
  def _construct_generic_dfa(self, base, a, name):
    r"""
    Run the recursion that constructs the generic DFA
    """
    # Begin with only the initial state
    qi = RSPGenericState(base,a,'initial',name)
    transitions = {}
    frontier = [qi]
    seen_states = set(frontier)
    while frontier != []:
      q = frontier.pop(0) 
      for next_q,t in q.out_states().items():
        edge = (q, next_q)
        transitions[edge] = t        
        if next_q in seen_states:
          # completed a cycle
          continue
        seen_states.add(next_q)
        frontier.append(next_q)
    return list(seen_states),transitions  

  ###########################  RSPGenericAutomaton  ############################

  def base(self):
    return self._base

  def a(self):
    return self._a

  def is_trimmed(self):
    return self._trimmed
  
  ###########################  RSPGenericAutomaton  ############################

  def states(self):
    r"""
    Return a list of copies of the states of self
    """
    return [q.copy() for q in self._states]

  def transitions(self):
    r"""
    Return a copy of the dict of transitions
    """
    D = {}
    for (q1,q2),t in self._transitions.items():
      D[(q1.copy(),q2.copy())] = t
    return D

  def transition(self, p, q):
    r"""
    Return the label on the transition p -> q, or None if no such exists
    """
    return self._transitions.get((p,q))

  def accepting_states(self):
    r"""
    Cache and return the list of accepting states
    """
    accepting = self._accepting_states
    if accepting is not None:
      return accepting
    accepting = [q for q in self._states if q.is_accepting()]
    accepting.sort()
    self._accepting_states = accepting
    return accepting

  def initial_state(self):
    r""" 
    Cache and return the initial state
    """
    qi = self._initial
    if qi is not None:
      return qi
    for q in self._states:
      if q.is_initial():
        qi = q
        break
    self._initial = qi
    return qi

  def odd_state(self):
    r"""
    Catche and return the odd state, if it exists
    """
    qodd = self._odd
    if qodd is not None:
      return qodd
    for q in self._states:
      if q.is_odd():
        qodd = q
        break
    self._odd = qodd
    return qodd
    
  def out_states(self, q):
    r"""
    Cache and return the list of outward states from q
    """
    outs = self._outs
    if outs is not None:
      return outs[q]
    self._outs = outs = {q:[] for q in self._states}
    for q1,q2 in self._transitions:
      outs[q1].append(q2)
    return outs[q]
  
  ###########################  RSPGenericAutomaton  ############################

  def num_states(self):
    return len(self._states)

  def num_transitions(self):
    return len(self._transitions)

  def num_accepting_states(self):
    return len(self.accepting_states())

  ###########################  RSPGenericAutomaton  ############################

  def minimum_specialization(self):
    r"""
    Return the minimum `T` at which specialization gives an RSPAutomaton object
    """
    min_spec = self._min_spec
    if min_spec is not None:
      return min_spec
    u,v = self._base
    minT = 0 if v >= 2 else 1  # uT + v >= 2 <==> T >= (2-v)/u
    while True:
      A = self(minT)
      if A is not None: break
      minT += 1
    self._min_spec = minT
    return minT
  
  ###########################  RSPGenericAutomaton  ############################

  def trim(self):
    r"""
    Return a trimmed verison of self
    """
    if self._trimmed:
      return

    accepting = self.accepting_states()
    if len(accepting) == 0:
      self._states = [self.initial_state()]
      self._transitions = {}
      self._outs = None
      self._initial = None
      self._odd = None
      self._accepting_states = None
      self._trimmed = True
      return

    # breadth-first search to determine states with no accessible accepting
    # state. Initial state will be a good state since the accepting set is
    # nonempty.
    bad_states = set()
    initial = self.initial_state()
    Q = self._states
    for q in Q:
      if q == self.initial_state(): continue
      frontier = [q]
      visited = set()
      while frontier != []:
        p = frontier.pop()
        if p in accepting:
          visited = set()
          break
        if p in visited:
          continue
        visited.add(p)
        for r in self.out_states(p):
          frontier.append(r)
      bad_states.update(visited)

    Q_new = [q for q in Q if q not in bad_states]
    Qset = set(Q_new)
    T_new = {}
    for (p,q),t in self._transitions.items():
      if p in Qset and q in Qset:
        T_new[(p,q)] = t
    self._states = Q_new
    self._transitions = T_new
    self._outs = None
    self._initial = initial
    self._odd = None
    self._accepting_states = None
    self._min_spec = None
    self._trimmed = True

  ###########################  RSPGenericAutomaton  ############################

  def __call__(self, t):
    r"""
    Return the specialization of self at the parameter t

    INPUT:

    - ``t`` -- a positive integer

    OUTPUT:

    - An RSPAutomaton object given by evaluating self._base and all edges in
      self._transitions at the parameter `T = t`. If this does not yield a valid
      RSPAutomaton because `t` is too small, then None is returned.

    """
    a = self._a
    u,v = self._base
    base = u*t + v
    if base < 2:
      return None
    
    states = {}
    for gen_state in self._states:
      state = gen_state(t)
      if state is None: return None
      states[gen_state] = state

    transitions = {}
    for (q1,q2),gen_char in self._transitions.items():
      char = gen_char(t)
      if char is None: return None
      s1,s2 = states[q1], states[q2]
      # Verify that outgoing states from initial state are valid
      if s1.is_initial() and s2.is_carry():
        _,b0 = char.char()
        if a + b0 >= base: return None
      transitions[(s1,s2)] = char

    states = list(states.values())
    return RSPAutomaton(None,None,states,transitions)

  ###########################  RSPGenericAutomaton  ############################      

  def sage_graph(self):
    r"""
    Return a Sage DiGraph object (if available)
    """
    try:
      from sage.graphs.digraph import DiGraph
    except ModuleNotFoundError:
      raise ModuleNotFoundError('Functionality only available in Sage')
    data = {}
    Ts = self._transitions
    for q1 in self._states:
      data[q1] = {q2:Ts[(q1,q2)] for q2 in self.out_states(q1)}
    return DiGraph(data,loops=True)

  ###########################  RSPGenericAutomaton  ############################

  def sage_plot(self, color1='palegoldenrod', color2='lightblue', 
                color3='palevioletred', vertex_labels=False, edge_labels=True, **kwargs):
    r"""
    Return a plot object using Sage (if available)

    INPUT:

    - ``color1, color2, color3`` -- strings recognized by MatPlotLib as colors

    - ``vertex_labels`` -- bool (default: False); whether to print vertex labels

    - ``edge_labels`` -- bool (default: True); whether to print edge labels

    - Additional keywords are passed to the plot() method.      

    OUTPUT:

    - A Sage plot object of self, with color1 indicating the initial state, 
      color2 indicating an accepting state, and color3 indicating a 
      non-accepting non-initial state

    NOTES:

    - To display this object in Sage, use the show() function.

    - Try plotting the same object several times; there is randomness in how Sage
      chooses the locations for the states.

    """
    verts1 = [self.initial_state()]
    verts2 = self.accepting_states()
    verts3 = [q for q in self._states if q not in verts1+verts2]
    vert_colors = {color1:verts1, color2:verts2, color3:verts3}

    G = self.sage_graph()
    a = self._a
    base = self._base
    name = self._name
    base_rep = generic_string(base,name)
    title = 'base = {}, a = {}'.format(base_rep,a)
      
    kwds = {}
    kwds['title'] = title
    kwds['vertex_colors'] = vert_colors
    kwds['vertex_labels'] = vertex_labels
    kwds['talk'] = vertex_labels # Use large vertices if vertex_labels is True
    kwds['edge_labels'] = edge_labels
    for key,val in kwargs.items():
      kwds[key] = val
    return G.plot(**kwds)
    
  ###########################  RSPGenericAutomaton  ############################
  
  def graphviz_graph(self):
    r"""
    Return a pygraphviz.AGraph object (if available)
    """
    try:
      from pygraphviz import AGraph
    except ModuleNotFoundError:
      msg = 'Functionality only available if pygraphviz is installed'
      raise ModuleNotFoundError(msg)

    G = AGraph(directed=True)
    for (q1,q2),label in self._transitions.items():
      G.add_edge(q1,q2,label=label)
    return G

  ###########################  RSPGenericAutomaton  ############################

  def graphviz_draw(self, filename=None, layout='dot', node_labels=False,
                    node_attributes=None, edge_labels=True, edge_attributes=None,
                    graph_attributes=None, colors=('khaki','lightblue','lightpink')):
    r"""
    Return a pygraphviz.AGraph object

    INPUT:

    - ``filename`` -- optional string to use for file to write output; extension
      will determine the file format. Typical choices are 'jpeg', 'jpg', 'png',
      'svg', 'ps','pdf','fig','dot', though there are many others.

    - ``layout`` -- string (default: 'dot'); layout style to use for drawing; 
      options are 'neato', 'dot', 'twopi', 'circo', or 'fdp'

    - ``node_labels`` -- bool (default: False); whether to print node labels

    - ``node_attributes`` -- optional dict whose keys are states of self and
      and whose values are dicts of additional attributes to be set for the
      associated pygraphviz.AGraph node objects

    - ``edge_labels`` -- bool (default: True); whether to print edge labels

    - ``edge_attributes`` -- optional dict whose keys are pairs of states of
      self and and whose values are dicts of additional attributes to be set for
      the associated pygraphviz.AGraph edge objects

    - ``graph_attributes`` -- optional dict of attributes to pass to the 
      pygraphviz.AGraph object; by default, only the directed attribute and 
      the label attribute are set

    - ``colors`` -- a triple of strings recognized by graphviz as colors

    OUTPUT:

    - A pygraphviz.AGraph object with all specified attributes set

    EFFECT:

    - Construct a pygraphviz.AGraph object and call its draw method, writing the
      output to ``filename``. If the colors specified are
      `(color1,color2,color3)`, then color1 is used for the initial state,
      color2 is used for the accepting states, and color3 is used for
      non-accepting non-initial states.

    BUG:

    - For some reason, when node_labels is set to True, one or more of the node
      labels is randomly set to None.

    """
    node_shape = 'oval' if node_labels else 'circle'
    node_label = lambda s : s if node_labels else ''
    edge_label = lambda s : s if edge_labels else ''    
    init_color,acc_color,gen_color = colors
    a = self._a
    base = self._base
    name = self._name
    base_rep = generic_string(base,name)
    title = 'base = {}, a = {}'.format(base_rep,a)
    if node_attributes is None: node_attributes = {}
    if edge_attributes is None: edge_attributes = {}
    if graph_attributes is None: graph_attributes = {}
    if 'label' not in graph_attributes:
      graph_attributes['label'] = title
    
    G = self.graphviz_graph()
    for attr,val in graph_attributes.items():
      G.graph_attr[attr] = val
    G.layout(prog=layout)
    
    for q in self._states:
      n = G.get_node(q)
      label = n.attr['label']
      n.attr['shape'] = node_shape
      n.attr['style'] = 'filled'
      n.attr['label'] = node_label(label)
      if node_shape == 'circle':
        n.attr['height'] = 0.25
        n.attr['width']  = 0.25
      if q.is_initial():
        n.attr['fillcolor'] = init_color
      elif q.is_accepting():
        n.attr['fillcolor'] = acc_color
      else:
        n.attr['fillcolor'] = gen_color
      q_attrs = node_attributes.get(q)
      if q_attrs is None: continue
      for attr,val in q_attrs.items():
        n.attr[attr] = val
      
    for (q1,q2) in self._transitions:
      e = G.get_edge(q1,q2)
      label = e.attr['label']
      e.attr['label'] = edge_label(label)
      e_attrs = edge_attributes.get((q1,q2))
      if e_attrs is None: continue
      for attr,val in e_attrs.items():
        e.attr[attr] = val
    if filename is not None:
      G.draw(filename)
    return G

# End RSPGenericAutomaton
