# Advanced Discrete Mathematics Review Notes
**MATH1064 - Enhanced Study Guide**

---

## 1 - Advanced Set Theory

### Set Operations and Properties

**Definition**: A set is a well-defined collection of distinct objects.

**Key Operations**:
- **Union**: A ∪ B = {x : x ∈ A ∨ x ∈ B}
- **Intersection**: A ∩ B = {x : x ∈ A ∧ x ∈ B}
- **Difference**: A \ B = {x : x ∈ A ∧ x ∉ B}
- **Complement**: A' = U \ A (where U is the universal set)
- **Symmetric Difference**: A △ B = (A \ B) ∪ (B \ A)

**De Morgan's Laws**:
1. (A ∪ B)' = A' ∩ B'
2. (A ∩ B)' = A' ∪ B'

**Proof Strategy**: For (A ∪ B)' = A' ∩ B'
- (⊆) Let x ∈ (A ∪ B)'. Then x ∉ A ∪ B, so x ∉ A and x ∉ B. Thus x ∈ A' and x ∈ B', so x ∈ A' ∩ B'.
- (⊇) Let x ∈ A' ∩ B'. Then x ∈ A' and x ∈ B', so x ∉ A and x ∉ B. Thus x ∉ A ∪ B, so x ∈ (A ∪ B)'.

### Double Containment Proof Technique

To prove A = B, show both:
1. A ⊆ B: For all x ∈ A, prove x ∈ B
2. B ⊆ A: For all x ∈ B, prove x ∈ A

**Example**: Prove A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)

### Power Sets and Cardinality


**Power Set**: P(A) = {S : S ⊆ A}
- If |A| = n, then |P(A)| = 2^n

**Cardinality Properties**:
- |A ∪ B| = |A| + |B| - |A ∩ B|
- |A × B| = |A| · |B|
- For finite sets: A ⊆ B ⟹ |A| ≤ |B|

---

## 2 - Functions, Relations, and Sequences

### Cartesian Product

**Definition**: A × B = {(a, b) : a ∈ A ∧ b ∈ B}

**Properties**:
- A × (B ∪ C) = (A × B) ∪ (A × C)
- A × (B ∩ C) = (A × B) ∩ (A × C)
- Generally NOT commutative: A × B ≠ B × A (unless A = B)

### Function Classification

**Injective (One-to-One)**: ∀x₁, x₂ ∈ X, f(x₁) = f(x₂) ⟹ x₁ = x₂
- Equivalently: x₁ ≠ x₂ ⟹ f(x₁) ≠ f(x₂)
- Horizontal line test: Each horizontal line intersects graph at most once

**Surjective (Onto)**: ∀y ∈ Y, ∃x ∈ X such that f(x) = y
- Range equals codomain
- Every element in Y is "hit" by some element in X

**Bijective**: Both injective and surjective
- Perfect one-to-one correspondence
- Has an inverse function f⁻¹: Y → X

### Proving Function Properties

**To prove f is injective**:
1. Assume f(x₁) = f(x₂)
2. Show x₁ = x₂

**To prove f is surjective**:
1. Let y ∈ Y be arbitrary
2. Find (or construct) x ∈ X such that f(x) = y

**To disprove injectivity**: Find x₁ ≠ x₂ with f(x₁) = f(x₂)
**To disprove surjectivity**: Find y ∈ Y with no preimage

### Composition of Functions


If f: X → Y and g: Y → Z, then g ∘ f: X → Z where (g ∘ f)(x) = g(f(x))

**Properties**:
- If f and g are injective, then g ∘ f is injective
- If f and g are surjective, then g ∘ f is surjective
- If f and g are bijective, then g ∘ f is bijective

### Sequences

**Definition**: A sequence is a function from ℕ (or ℕ₀) to a set S
- Notation: {aₙ} or (a₁, a₂, a₃, ...)

**Arithmetic Sequence**: aₙ = a₁ + (n-1)d
- Sum: Sₙ = n(a₁ + aₙ)/2 = n(2a₁ + (n-1)d)/2

**Geometric Sequence**: aₙ = a₁ · rⁿ⁻¹
- Sum: Sₙ = a₁(1 - rⁿ)/(1 - r) for r ≠ 1
- Infinite sum (|r| < 1): S = a₁/(1 - r)

---

## 3 - Number Theory: Divisibility and Primes

### Divisibility

**Definition**: a | b (a divides b) if ∃k ∈ ℤ such that b = ak

**Properties**:
1. a | b and b | c ⟹ a | c (transitivity)
2. a | b and a | c ⟹ a | (bx + cy) for any x, y ∈ ℤ
3. a | b and b | a ⟹ a = ±b
4. a | b and b ≠ 0 ⟹ |a| ≤ |b|

### Division Algorithm (Quotient-Remainder Theorem)

**Theorem**: For any integers a and b with b > 0, there exist unique integers q and r such that:
- a = bq + r where 0 ≤ r < b
- q is the quotient, r is the remainder

### Modular Arithmetic

**Definition**: a ≡ b (mod m) if m | (a - b)

**Properties**:
1. Reflexive: a ≡ a (mod m)
2. Symmetric: a ≡ b (mod m) ⟹ b ≡ a (mod m)
3. Transitive: a ≡ b (mod m) and b ≡ c (mod m) ⟹ a ≡ c (mod m)

**Arithmetic Operations**:
- If a ≡ b (mod m) and c ≡ d (mod m), then:
  - a + c ≡ b + d (mod m)
  - a - c ≡ b - d (mod m)
  - ac ≡ bd (mod m)
  - aⁿ ≡ bⁿ (mod m) for n ≥ 0


### Prime Numbers

**Definition**: p > 1 is prime if its only positive divisors are 1 and p

**Fundamental Theorem of Arithmetic**: Every integer n > 1 can be uniquely expressed as a product of primes (up to order):
n = p₁^a₁ · p₂^a₂ · ... · pₖ^aₖ

**Euclid's Lemma**: If p is prime and p | ab, then p | a or p | b

**Infinitude of Primes**: There are infinitely many primes (Euclid's proof by contradiction)

### GCD and LCM

**Greatest Common Divisor**: gcd(a, b) is the largest positive integer that divides both a and b

**Properties**:
- gcd(a, b) = gcd(b, a)
- gcd(a, 0) = |a|
- gcd(a, b) = gcd(a - b, b)
- If a = bq + r, then gcd(a, b) = gcd(b, r)

**Least Common Multiple**: lcm(a, b) is the smallest positive integer divisible by both a and b

**Key Relationship**: gcd(a, b) · lcm(a, b) = |ab|

### Euclidean Algorithm

**Algorithm** to find gcd(a, b):
1. If b = 0, return a
2. Otherwise, return gcd(b, a mod b)

**Example**: gcd(252, 105)
- 252 = 105 · 2 + 42
- 105 = 42 · 2 + 21
- 42 = 21 · 2 + 0
- Therefore, gcd(252, 105) = 21

**Extended Euclidean Algorithm**: Finds integers x, y such that ax + by = gcd(a, b)

### Base Representations

**Base b expansion**: n = aₖb^k + aₖ₋₁b^(k-1) + ... + a₁b + a₀
- Binary (b=2), Octal (b=8), Decimal (b=10), Hexadecimal (b=16)

**Conversion Algorithm** (decimal to base b):
1. Divide n by b, record remainder
2. Replace n with quotient
3. Repeat until n = 0
4. Read remainders in reverse order

---

## 4 - Combinatorics: Counting Principles

### Fundamental Counting Principles

**Product Rule**: If task 1 can be done in n₁ ways and task 2 in n₂ ways, then both can be done in n₁ · n₂ ways

**Sum Rule**: If task 1 can be done in n₁ ways and task 2 in n₂ ways (mutually exclusive), then either can be done in n₁ + n₂ ways


### Permutations and Combinations

**Permutations** (order matters):
- P(n, k) = n!/(n-k)! = n(n-1)(n-2)...(n-k+1)
- Number of ways to arrange k items from n items

**Combinations** (order doesn't matter):
- C(n, k) = n!/(k!(n-k)!) = (n choose k)
- Number of ways to choose k items from n items

**Key Identities**:
- C(n, k) = C(n, n-k)
- C(n, 0) = C(n, n) = 1
- C(n, k) = C(n-1, k-1) + C(n-1, k) (Pascal's Identity)

### Permutations with Repetition

**Formula**: n!/(n₁! · n₂! · ... · nₖ!)
- n total objects with n₁ of type 1, n₂ of type 2, etc.

**Example**: Arrangements of "MISSISSIPPI"
- 11!/(1! · 4! · 4! · 2!) = 34,650

### Stars and Bars

**Problem**: Distribute n identical objects into k distinct bins

**Formula**: C(n + k - 1, k - 1) = C(n + k - 1, n)

**With minimum constraints**: If each bin must have at least 1 object:
C(n - 1, k - 1)

---

## 5 - Advanced Combinatorics

### Binomial Theorem

**Theorem**: (x + y)ⁿ = Σ(k=0 to n) C(n,k) · xⁿ⁻ᵏ · yᵏ

**Special Cases**:
- (1 + x)ⁿ = Σ(k=0 to n) C(n,k) · xᵏ
- Setting x = y = 1: 2ⁿ = Σ(k=0 to n) C(n,k)
- Setting x = 1, y = -1: 0 = Σ(k=0 to n) (-1)ᵏ · C(n,k)

**Pascal's Triangle**:
```
       1
      1 1
     1 2 1
    1 3 3 1
   1 4 6 4 1
```

### Inclusion-Exclusion Principle

**Two Sets**: |A ∪ B| = |A| + |B| - |A ∩ B|

**Three Sets**: |A ∪ B ∪ C| = |A| + |B| + |C| - |A ∩ B| - |A ∩ C| - |B ∩ C| + |A ∩ B ∩ C|

**General Formula**: 
|A₁ ∪ A₂ ∪ ... ∪ Aₙ| = Σ|Aᵢ| - Σ|Aᵢ ∩ Aⱼ| + Σ|Aᵢ ∩ Aⱼ ∩ Aₖ| - ... + (-1)ⁿ⁺¹|A₁ ∩ ... ∩ Aₙ|


**Application - Derangements**: Number of permutations with no fixed points
Dₙ = n! · Σ(k=0 to n) (-1)ᵏ/k! ≈ n!/e

### Pigeonhole Principle

**Simple Form**: If n+1 objects are placed into n boxes, at least one box contains at least 2 objects

**Generalized Form**: If N objects are placed into k boxes, at least one box contains at least ⌈N/k⌉ objects

**Applications**:
- In any group of 13 people, at least 2 share a birth month
- Among n+1 integers, at least 2 have the same remainder when divided by n

### Catalan Numbers

**Definition**: Cₙ = C(2n, n)/(n+1) = (2n)!/((n+1)! · n!)

**Recursive Formula**: C₀ = 1, Cₙ₊₁ = Σ(i=0 to n) Cᵢ · Cₙ₋ᵢ

**First few values**: 1, 1, 2, 5, 14, 42, 132, 429, ...

**Applications**:
1. Number of valid parentheses sequences of length 2n
2. Number of binary trees with n+1 leaves
3. Number of ways to triangulate a convex (n+2)-gon
4. Number of paths from (0,0) to (n,n) that don't cross diagonal y=x

**Example**: C₃ = 5 valid parentheses: ((())), (()()), (())(), ()(()), ()()()

---

## 6 - Probability Theory

### Sample Spaces and Events

**Sample Space** (Ω): Set of all possible outcomes
**Event**: Subset of sample space
**Probability Function**: P: Events → [0,1] satisfying:
1. P(Ω) = 1
2. P(A) ≥ 0 for all events A
3. P(A ∪ B) = P(A) + P(B) if A ∩ B = ∅

### Probability Rules

**Complement Rule**: P(A') = 1 - P(A)

**Addition Rule**: P(A ∪ B) = P(A) + P(B) - P(A ∩ B)

**Conditional Probability**: P(A|B) = P(A ∩ B)/P(B) if P(B) > 0

**Multiplication Rule**: P(A ∩ B) = P(A|B) · P(B) = P(B|A) · P(A)

### Independence

**Definition**: Events A and B are independent if P(A ∩ B) = P(A) · P(B)

**Equivalent conditions**:
- P(A|B) = P(A)
- P(B|A) = P(B)

**Pairwise vs Mutual Independence**: Events A₁, ..., Aₙ are mutually independent if for every subset I ⊆ {1,...,n}:
P(∩ᵢ∈ᵢ Aᵢ) = ∏ᵢ∈ᵢ P(Aᵢ)


### Bayes' Theorem

**Theorem**: P(A|B) = P(B|A) · P(A) / P(B)

**Extended Form** (Law of Total Probability):
If B₁, ..., Bₙ partition the sample space, then:
P(A|Bᵢ) = P(Bᵢ|A) · P(Bᵢ) / Σⱼ P(Bⱼ|A) · P(Bⱼ)

**Application**: Medical testing, spam filtering, machine learning

### Random Variables

**Definition**: A function X: Ω → ℝ mapping outcomes to real numbers

**Discrete Random Variable**: Takes countably many values

**Probability Mass Function (PMF)**: p(x) = P(X = x)
- Σₓ p(x) = 1

**Common Distributions**:

1. **Bernoulli(p)**: X ∈ {0, 1}
   - P(X = 1) = p, P(X = 0) = 1 - p

2. **Binomial(n, p)**: Number of successes in n trials
   - P(X = k) = C(n,k) · pᵏ · (1-p)ⁿ⁻ᵏ

3. **Geometric(p)**: Number of trials until first success
   - P(X = k) = (1-p)ᵏ⁻¹ · p

4. **Poisson(λ)**: Number of events in fixed interval
   - P(X = k) = e⁻λ · λᵏ / k!

### Expected Value

**Definition**: E[X] = Σₓ x · P(X = x)

**Properties**:
1. E[aX + b] = aE[X] + b (linearity)
2. E[X + Y] = E[X] + E[Y] (always true)
3. E[XY] = E[X] · E[Y] (if X, Y independent)

**Expected Values of Common Distributions**:
- Bernoulli(p): E[X] = p
- Binomial(n, p): E[X] = np
- Geometric(p): E[X] = 1/p
- Poisson(λ): E[X] = λ

### Variance and Standard Deviation

**Variance**: Var(X) = E[(X - E[X])²] = E[X²] - (E[X])²

**Standard Deviation**: σ(X) = √Var(X)

**Properties**:
1. Var(aX + b) = a² · Var(X)
2. Var(X + Y) = Var(X) + Var(Y) if X, Y independent
3. Var(X) ≥ 0, with equality iff X is constant

**Variances of Common Distributions**:
- Bernoulli(p): Var(X) = p(1-p)
- Binomial(n, p): Var(X) = np(1-p)
- Geometric(p): Var(X) = (1-p)/p²
- Poisson(λ): Var(X) = λ


---

## 7 - Graph Theory Fundamentals

### Basic Definitions

**Graph**: G = (V, E) where V is a set of vertices and E is a set of edges

**Simple Graph**: No loops or multiple edges
- Undirected: edges are unordered pairs {u, v}
- At most C(n, 2) = n(n-1)/2 edges for n vertices

**Degree**: deg(v) = number of edges incident to v
- In directed graphs: in-degree and out-degree

### Handshake Theorem

**Theorem**: Σᵥ∈V deg(v) = 2|E|

**Proof**: Each edge contributes 2 to the sum (once for each endpoint)

**Corollary**: Every graph has an even number of odd-degree vertices

**Proof**: Let O = odd-degree vertices, E = even-degree vertices
- Σᵥ∈O deg(v) + Σᵥ∈E deg(v) = 2|E|
- Since right side is even and second sum is even, first sum must be even
- Since each term in first sum is odd, |O| must be even

### Special Graphs

**Complete Graph** Kₙ: Every pair of vertices is connected
- |E| = C(n, 2) = n(n-1)/2
- deg(v) = n-1 for all v

**Cycle** Cₙ: n vertices in a circle
- |E| = n
- deg(v) = 2 for all v

**Path** Pₙ: n vertices in a line
- |E| = n-1
- Two vertices have degree 1, rest have degree 2

**Bipartite Graph**: V = V₁ ∪ V₂, all edges between V₁ and V₂
- Complete bipartite Kₘ,ₙ has m·n edges

**Tree**: Connected acyclic graph
- |E| = |V| - 1
- Unique path between any two vertices

### Paths and Circuits

**Walk**: Sequence of vertices v₀, v₁, ..., vₖ where each consecutive pair is connected

**Path**: Walk with no repeated vertices

**Circuit/Cycle**: Walk that starts and ends at same vertex

**Simple Path**: Path with no repeated edges

**Euler Circuit**: Circuit using every edge exactly once
- **Theorem**: Connected graph has Euler circuit ⟺ every vertex has even degree

**Euler Path**: Path using every edge exactly once
- **Theorem**: Connected graph has Euler path ⟺ exactly 0 or 2 vertices have odd degree

**Hamilton Circuit**: Circuit visiting every vertex exactly once
- No simple characterization (NP-complete problem)


### Graph Isomorphism

**Definition**: Graphs G₁ = (V₁, E₁) and G₂ = (V₂, E₂) are isomorphic if there exists a bijection f: V₁ → V₂ such that:
{u, v} ∈ E₁ ⟺ {f(u), f(v)} ∈ E₂

**Graph Invariants** (preserved under isomorphism):
1. Number of vertices
2. Number of edges
3. Degree sequence (sorted list of degrees)
4. Number of cycles of each length
5. Chromatic number
6. Diameter and radius

**To prove graphs are NOT isomorphic**: Find a graph invariant that differs

**To prove graphs ARE isomorphic**: Construct explicit bijection

### Adjacency Matrix

**Definition**: For graph with vertices v₁, ..., vₙ, adjacency matrix A is n×n where:
- Aᵢⱼ = 1 if {vᵢ, vⱼ} ∈ E
- Aᵢⱼ = 0 otherwise

**Properties**:
- Symmetric for undirected graphs
- (Aᵏ)ᵢⱼ = number of walks of length k from vᵢ to vⱼ
- Trace(A) = 0 for simple graphs (no loops)

### Connectivity

**Connected Graph**: Path exists between every pair of vertices

**Connected Components**: Maximal connected subgraphs

**Cut Vertex**: Vertex whose removal increases number of components

**Bridge**: Edge whose removal increases number of components

**k-Connected**: Remains connected after removing any k-1 vertices

---

## 8 - Relations and Partial Orders

### Binary Relations

**Definition**: R ⊆ A × B is a relation from A to B
- Write aRb or (a,b) ∈ R

**Properties of Relations on A**:

1. **Reflexive**: ∀a ∈ A, aRa
2. **Symmetric**: ∀a,b ∈ A, aRb ⟹ bRa
3. **Antisymmetric**: ∀a,b ∈ A, (aRb ∧ bRa) ⟹ a = b
4. **Transitive**: ∀a,b,c ∈ A, (aRb ∧ bRc) ⟹ aRc

### Equivalence Relations

**Definition**: Relation that is reflexive, symmetric, and transitive

**Examples**:
- Equality (=)
- Congruence modulo n (≡ₙ)
- "Has same birthday as"
- Set equality

**Equivalence Class**: [a] = {b ∈ A : aRb}
- All elements equivalent to a

**Properties**:
1. a ∈ [a] (non-empty)
2. aRb ⟺ [a] = [b]
3. [a] ∩ [b] = ∅ or [a] = [b]


### Partitions

**Definition**: Collection of non-empty, pairwise disjoint subsets whose union is A

**Theorem**: Equivalence relations on A correspond bijectively to partitions of A
- Equivalence classes form a partition
- Each partition defines an equivalence relation

**Example**: ℤ partitioned by congruence mod 3:
- [0] = {..., -6, -3, 0, 3, 6, ...}
- [1] = {..., -5, -2, 1, 4, 7, ...}
- [2] = {..., -4, -1, 2, 5, 8, ...}

### Partial Orders

**Definition**: Relation that is reflexive, antisymmetric, and transitive

**Examples**:
- ≤ on ℝ
- ⊆ on P(A)
- Divisibility | on ℕ

**Total Order**: Partial order where every pair is comparable
- ∀a,b: aRb or bRa

**Poset**: (A, ≤) is a partially ordered set

**Hasse Diagram**: Visual representation of poset
- Draw vertices for elements
- Draw edge from a to b if a < b and no c with a < c < b
- Arrange so smaller elements are lower

**Maximal Element**: m where no element is greater than m
**Maximum Element**: m where m ≥ a for all a

**Minimal Element**: m where no element is less than m
**Minimum Element**: m where m ≤ a for all a

### Closures

**Reflexive Closure**: Smallest reflexive relation containing R
- R ∪ {(a,a) : a ∈ A}

**Symmetric Closure**: Smallest symmetric relation containing R
- R ∪ {(b,a) : (a,b) ∈ R}

**Transitive Closure**: Smallest transitive relation containing R
- R⁺ = R ∪ R² ∪ R³ ∪ ...
- Can compute using Warshall's algorithm

**Connectivity Relation**: Transitive closure of graph relation
- aR*b if there exists a path from a to b

---

## 9 - Propositional Logic

### Logical Connectives

**Negation**: ¬p (NOT p)
**Conjunction**: p ∧ q (p AND q)
**Disjunction**: p ∨ q (p OR q)
**Exclusive Or**: p ⊕ q (p XOR q)
**Conditional**: p → q (if p then q)
**Biconditional**: p ↔ q (p if and only if q)

### Truth Tables

| p | q | ¬p | p∧q | p∨q | p⊕q | p→q | p↔q |
|---|---|----|----|----|----|----|----|
| T | T | F  | T  | T  | F  | T  | T  |
| T | F | F  | F  | T  | T  | F  | F  |
| F | T | T  | F  | T  | T  | T  | F  |
| F | F | T  | F  | F  | F  | T  | T  |


### Logical Equivalences

**De Morgan's Laws**:
- ¬(p ∧ q) ≡ ¬p ∨ ¬q
- ¬(p ∨ q) ≡ ¬p ∧ ¬q

**Conditional Equivalences**:
- p → q ≡ ¬p ∨ q
- p → q ≡ ¬q → ¬p (contrapositive)
- ¬(p → q) ≡ p ∧ ¬q

**Biconditional**:
- p ↔ q ≡ (p → q) ∧ (q → p)
- p ↔ q ≡ (p ∧ q) ∨ (¬p ∧ ¬q)

**Distributive Laws**:
- p ∧ (q ∨ r) ≡ (p ∧ q) ∨ (p ∧ r)
- p ∨ (q ∧ r) ≡ (p ∨ q) ∧ (p ∨ r)

### Tautologies and Contradictions

**Tautology**: Always true (e.g., p ∨ ¬p)
**Contradiction**: Always false (e.g., p ∧ ¬p)
**Contingency**: Sometimes true, sometimes false

### Predicates and Quantifiers

**Predicate**: P(x) is a statement about x that becomes true/false when x is specified

**Universal Quantifier**: ∀x P(x) means "P(x) is true for all x"
**Existential Quantifier**: ∃x P(x) means "P(x) is true for some x"

**Negation Rules**:
- ¬(∀x P(x)) ≡ ∃x ¬P(x)
- ¬(∃x P(x)) ≡ ∀x ¬P(x)

**Multiple Quantifiers**:
- ∀x ∀y P(x,y) ≡ ∀y ∀x P(x,y)
- ∃x ∃y P(x,y) ≡ ∃y ∃x P(x,y)
- ∀x ∃y P(x,y) ≠ ∃y ∀x P(x,y) (order matters!)

**Example**: Let P(x,y) = "x loves y"
- ∀x ∃y P(x,y): Everyone loves someone
- ∃y ∀x P(x,y): Someone is loved by everyone

### Valid Arguments

**Modus Ponens**: p, p → q ⊢ q
**Modus Tollens**: ¬q, p → q ⊢ ¬p
**Hypothetical Syllogism**: p → q, q → r ⊢ p → r
**Disjunctive Syllogism**: p ∨ q, ¬p ⊢ q
**Addition**: p ⊢ p ∨ q
**Simplification**: p ∧ q ⊢ p
**Conjunction**: p, q ⊢ p ∧ q
**Resolution**: p ∨ q, ¬p ∨ r ⊢ q ∨ r

**Universal Instantiation**: ∀x P(x) ⊢ P(c) for any c
**Universal Generalization**: P(c) for arbitrary c ⊢ ∀x P(x)
**Existential Instantiation**: ∃x P(x) ⊢ P(c) for some c
**Existential Generalization**: P(c) ⊢ ∃x P(x)

---

## 10 - Proof Techniques

### Direct Proof

**Structure**: To prove p → q
1. Assume p is true
2. Use definitions, axioms, and previously proven theorems
3. Derive q

**Example**: Prove that if n is odd, then n² is odd
- Assume n is odd, so n = 2k+1 for some integer k
- Then n² = (2k+1)² = 4k² + 4k + 1 = 2(2k² + 2k) + 1
- This is of the form 2m+1, so n² is odd


### Proof by Contrapositive

**Structure**: To prove p → q, instead prove ¬q → ¬p

**When to use**: When ¬q gives more information to work with than p

**Example**: Prove that if n² is even, then n is even
- Contrapositive: If n is odd, then n² is odd
- (Already proved above)

### Proof by Contradiction

**Structure**: To prove p
1. Assume ¬p
2. Derive a contradiction
3. Conclude p must be true

**Example**: Prove √2 is irrational
- Assume √2 = a/b where a,b are integers in lowest terms
- Then 2 = a²/b², so 2b² = a²
- Thus a² is even, so a is even, say a = 2k
- Then 2b² = 4k², so b² = 2k²
- Thus b² is even, so b is even
- But then both a and b are even, contradicting lowest terms
- Therefore √2 is irrational

### Proof by Cases

**Structure**: To prove p
1. Show p₁ ∨ p₂ ∨ ... ∨ pₙ (exhaustive cases)
2. Prove p in each case

**Example**: Prove n² + n is even for all integers n
- Case 1: n is even, say n = 2k. Then n² + n = 4k² + 2k = 2(2k² + k), which is even
- Case 2: n is odd, say n = 2k+1. Then n² + n = (2k+1)² + (2k+1) = 4k² + 4k + 1 + 2k + 1 = 4k² + 6k + 2 = 2(2k² + 3k + 1), which is even

### Existence Proofs

**Constructive**: Explicitly find an example
**Non-constructive**: Prove existence without finding example

**Example (Constructive)**: There exists an even prime
- 2 is even and prime

**Example (Non-constructive)**: There exist irrational numbers a, b such that a^b is rational
- Consider √2^√2. If rational, we're done (a = b = √2)
- If irrational, let a = √2^√2 and b = √2. Then a^b = (√2^√2)^√2 = √2^(√2·√2) = √2^2 = 2, which is rational

### Uniqueness Proofs

**Structure**: To prove "there exists a unique x such that P(x)"
1. Existence: Show some x satisfies P(x)
2. Uniqueness: Show if x₁ and x₂ both satisfy P(x), then x₁ = x₂

---

## 11 - Mathematical Induction

### Principle of Mathematical Induction

**Structure**: To prove P(n) for all n ≥ n₀
1. **Base Case**: Prove P(n₀)
2. **Inductive Step**: Prove P(k) → P(k+1) for arbitrary k ≥ n₀
   - Assume P(k) (inductive hypothesis)
   - Prove P(k+1)
3. **Conclusion**: By induction, P(n) holds for all n ≥ n₀


**Example**: Prove 1 + 2 + ... + n = n(n+1)/2

*Base case*: n = 1. LHS = 1, RHS = 1(2)/2 = 1. ✓

*Inductive step*: Assume 1 + 2 + ... + k = k(k+1)/2
Then 1 + 2 + ... + k + (k+1) = k(k+1)/2 + (k+1)
                                = (k(k+1) + 2(k+1))/2
                                = (k+1)(k+2)/2
                                = (k+1)((k+1)+1)/2 ✓

*Conclusion*: By induction, the formula holds for all n ≥ 1.

### Strong Induction

**Structure**: To prove P(n) for all n ≥ n₀
1. **Base Case**: Prove P(n₀), P(n₀+1), ..., P(n₁) (may need multiple)
2. **Inductive Step**: Assume P(n₀), P(n₀+1), ..., P(k) all true, prove P(k+1)
3. **Conclusion**: By strong induction, P(n) holds for all n ≥ n₀

**When to use**: When proving P(k+1) requires knowing P(j) for multiple j ≤ k

**Example**: Prove every integer n ≥ 2 can be written as a product of primes

*Base case*: n = 2 is prime. ✓

*Inductive step*: Assume all integers from 2 to k can be written as products of primes.
Consider k+1:
- If k+1 is prime, done
- If k+1 is composite, then k+1 = ab where 2 ≤ a, b ≤ k
- By inductive hypothesis, both a and b are products of primes
- Therefore k+1 is a product of primes ✓

### Structural Induction

Used for recursively defined structures (trees, lists, etc.)

**Example**: Prove all binary trees with n internal nodes have n+1 leaves

*Base case*: Tree with 0 internal nodes (single leaf) has 1 leaf. ✓

*Inductive step*: Assume true for trees with ≤ k internal nodes.
Consider tree T with k+1 internal nodes. Root has left subtree L and right subtree R.
- L has i internal nodes, R has j internal nodes, where i + j + 1 = k + 1
- By IH, L has i+1 leaves and R has j+1 leaves
- T has (i+1) + (j+1) = i + j + 2 = (k+1) + 1 leaves ✓

### Recursion

**Recursive Definition**: Define function in terms of itself on smaller inputs

**Example - Fibonacci**: F(0) = 0, F(1) = 1, F(n) = F(n-1) + F(n-2) for n ≥ 2

**Example - Factorial**: 0! = 1, n! = n · (n-1)! for n ≥ 1

**Recursive Algorithms**: Must have:
1. Base case(s)
2. Recursive case(s) that make progress toward base case
3. Termination guarantee


### Big-O Notation

**Definition**: f(n) = O(g(n)) if ∃c > 0, n₀ such that |f(n)| ≤ c|g(n)| for all n ≥ n₀

**Intuition**: f grows no faster than g (up to constant factor)

**Common Growth Rates** (from slowest to fastest):
- O(1) - constant
- O(log n) - logarithmic
- O(n) - linear
- O(n log n) - linearithmic
- O(n²) - quadratic
- O(n³) - cubic
- O(2ⁿ) - exponential
- O(n!) - factorial

**Properties**:
1. If f(n) = O(g(n)) and g(n) = O(h(n)), then f(n) = O(h(n))
2. f(n) + g(n) = O(max(f(n), g(n)))
3. c · f(n) = O(f(n)) for constant c
4. f(n) · g(n) = O(f(n) · g(n))

**Big-Ω Notation**: f(n) = Ω(g(n)) if g(n) = O(f(n))
- Lower bound: f grows at least as fast as g

**Big-Θ Notation**: f(n) = Θ(g(n)) if f(n) = O(g(n)) and f(n) = Ω(g(n))
- Tight bound: f and g grow at same rate

**Example**: Prove 3n² + 5n + 2 = O(n²)
- Need to show 3n² + 5n + 2 ≤ c·n² for some c and all n ≥ n₀
- For n ≥ 1: 3n² + 5n + 2 ≤ 3n² + 5n² + 2n² = 10n²
- So choose c = 10, n₀ = 1

---

## 12 - Complexity and Computation

### Algorithm Analysis

**Time Complexity**: Number of basic operations as function of input size

**Space Complexity**: Amount of memory used as function of input size

**Best/Worst/Average Case**: Different scenarios for same algorithm

**Example - Linear Search**:
- Best case: O(1) - element is first
- Worst case: O(n) - element is last or not present
- Average case: O(n) - element in middle on average

**Example - Binary Search** (sorted array):
- All cases: O(log n)

**Example - Sorting Algorithms**:
- Bubble Sort: O(n²)
- Merge Sort: O(n log n)
- Quick Sort: O(n log n) average, O(n²) worst
- Counting Sort: O(n + k) where k is range

### Recurrence Relations

**Definition**: Equation defining sequence in terms of previous terms

**Example**: T(n) = 2T(n/2) + n (merge sort)

**Master Theorem**: For T(n) = aT(n/b) + f(n)
1. If f(n) = O(n^(log_b(a) - ε)) for ε > 0, then T(n) = Θ(n^log_b(a))
2. If f(n) = Θ(n^log_b(a)), then T(n) = Θ(n^log_b(a) · log n)
3. If f(n) = Ω(n^(log_b(a) + ε)) and regularity condition, then T(n) = Θ(f(n))


### Formal Languages

**Alphabet** Σ: Finite set of symbols

**String**: Finite sequence of symbols from Σ
- Empty string: ε or λ
- Length: |w|
- Concatenation: w₁w₂

**Language**: Set of strings over Σ
- L ⊆ Σ*

**Operations on Languages**:
- Union: L₁ ∪ L₂
- Concatenation: L₁L₂ = {w₁w₂ : w₁ ∈ L₁, w₂ ∈ L₂}
- Kleene Star: L* = {ε} ∪ L ∪ LL ∪ LLL ∪ ...

### Phrase-Structure Grammars

**Grammar**: G = (V, T, S, P) where:
- V: variables (non-terminals)
- T: terminals
- S: start symbol
- P: production rules

**Chomsky Hierarchy**:
1. **Type 0** (Unrestricted): α → β where α contains at least one variable
2. **Type 1** (Context-Sensitive): αAβ → αγβ where |γ| ≥ 1
3. **Type 2** (Context-Free): A → γ
4. **Type 3** (Regular): A → aB or A → a

**Example - Balanced Parentheses** (Context-Free):
- S → (S) | SS | ε

**Derivation**: Sequence of applications of production rules
- Leftmost: Always replace leftmost variable
- Rightmost: Always replace rightmost variable

### Finite-State Machines

**Deterministic FSM**: M = (S, I, O, f, g, s₀) where:
- S: finite set of states
- I: input alphabet
- O: output alphabet
- f: S × I → S (transition function)
- g: S × I → O (output function)
- s₀: initial state

**Types**:
- **Moore Machine**: Output depends only on state
- **Mealy Machine**: Output depends on state and input

**State Diagram**: Visual representation
- Nodes: states
- Edges: transitions labeled with input/output

**Example - Parity Checker**:
- States: {even, odd}
- Input: {0, 1}
- Transition: flip state on input 1, stay on input 0
- Output: current state

---

## 13 - Automata and Regular Languages

### Finite-State Automata (FSA)

**Deterministic FSA**: M = (Q, Σ, δ, q₀, F) where:
- Q: finite set of states
- Σ: input alphabet
- δ: Q × Σ → Q (transition function)
- q₀: initial state
- F ⊆ Q: accepting states

**Language Accepted**: L(M) = {w : δ*(q₀, w) ∈ F}


**Nondeterministic FSA (NFA)**: δ: Q × Σ → P(Q)
- Can have multiple transitions for same input
- Can have ε-transitions (move without consuming input)

**Theorem**: Every NFA has an equivalent DFA
- Subset construction: DFA states are subsets of NFA states

### Regular Languages

**Definition**: Language is regular if accepted by some FSA

**Regular Expressions**: Notation for regular languages
- ∅: empty language
- ε: language containing only empty string
- a: language containing only string "a"
- r₁ ∪ r₂: union
- r₁r₂: concatenation
- r*: Kleene star (zero or more repetitions)

**Examples**:
- (0|1)*: all binary strings
- (0|1)*1: binary strings ending in 1
- (a|b)*abb: strings over {a,b} ending in "abb"

**Kleene's Theorem**: Language is regular ⟺ it can be described by a regular expression

**Closure Properties**: Regular languages are closed under:
- Union, intersection, complement
- Concatenation, Kleene star
- Reversal, homomorphism

**Pumping Lemma for Regular Languages**:
If L is regular, then ∃p (pumping length) such that:
For any string s ∈ L with |s| ≥ p, we can write s = xyz where:
1. |xy| ≤ p
2. |y| > 0
3. xy^i z ∈ L for all i ≥ 0

**Use**: To prove a language is NOT regular

**Example**: Prove L = {0ⁿ1ⁿ : n ≥ 0} is not regular
- Assume L is regular with pumping length p
- Consider s = 0^p 1^p ∈ L
- By pumping lemma, s = xyz with |xy| ≤ p, |y| > 0
- Since |xy| ≤ p, y consists only of 0's
- But then xyyz = 0^(p+|y|) 1^p ∉ L
- Contradiction, so L is not regular

### Context-Free Languages

**Pushdown Automaton (PDA)**: FSA with a stack
- Can recognize context-free languages
- Example: {0ⁿ1ⁿ : n ≥ 0} is context-free but not regular

**Pumping Lemma for CFLs**: Similar to regular languages but more complex

**Closure Properties**: CFLs are closed under:
- Union, concatenation, Kleene star
- NOT closed under intersection or complement

---

## Advanced Problem-Solving Strategies

### General Approach

1. **Understand the Problem**
   - What is given? What needs to be proved/found?
   - What are the constraints?

2. **Devise a Plan**
   - Have you seen a similar problem?
   - Can you use a known theorem or technique?
   - Can you solve a simpler version first?

3. **Carry Out the Plan**
   - Be systematic and rigorous
   - Check each step

4. **Look Back**
   - Does the answer make sense?
   - Can you verify it?
   - Can you generalize?


### Common Proof Patterns

**To prove A = B (sets)**:
- Double containment: A ⊆ B and B ⊆ A
- Element argument: x ∈ A ⟺ x ∈ B

**To prove f is bijective**:
- Show f is injective and surjective
- Or construct explicit inverse f⁻¹

**To prove divisibility**:
- Use definition: show b = ak for some integer k
- Use properties of divisibility

**To prove congruence**:
- Show m | (a - b)
- Use modular arithmetic properties

**To prove graph property**:
- Use graph invariants
- Apply known theorems (handshake, Euler, etc.)

**To prove formula by induction**:
- Verify base case carefully
- In inductive step, clearly state IH and show how it's used
- Algebraic manipulation to reach desired form

### Common Mistakes to Avoid

1. **Assuming what you're trying to prove**
   - Don't start with the conclusion

2. **Confusing necessary and sufficient conditions**
   - p → q doesn't mean q → p

3. **Misusing quantifiers**
   - Order matters: ∀x ∃y ≠ ∃y ∀x

4. **Incomplete case analysis**
   - Make sure cases are exhaustive

5. **Circular reasoning**
   - Don't use result to prove itself

6. **Arithmetic errors**
   - Double-check algebra and arithmetic

7. **Forgetting edge cases**
   - Empty set, n=0, n=1, etc.

### Exam Strategies

**Time Management**:
- Read all questions first
- Do easier problems first
- Leave time to check work

**Problem-Solving**:
- Write clearly and organize work
- Show all steps
- State theorems/definitions used
- Draw diagrams when helpful

**Proofs**:
- State what you're proving
- Identify proof technique
- Be explicit about assumptions
- End with clear conclusion

**Calculations**:
- Show intermediate steps
- Label final answer
- Check reasonableness

---

## Key Formulas Reference

### Combinatorics
- P(n,k) = n!/(n-k)!
- C(n,k) = n!/(k!(n-k)!)
- Stars and bars: C(n+k-1, k-1)
- Catalan: Cₙ = C(2n,n)/(n+1)

### Number Theory
- gcd(a,b) · lcm(a,b) = |ab|
- a ≡ b (mod m) ⟺ m | (a-b)

### Probability
- P(A ∪ B) = P(A) + P(B) - P(A ∩ B)
- P(A|B) = P(A ∩ B)/P(B)
- E[X] = Σ x · P(X=x)
- Var(X) = E[X²] - (E[X])²

### Graph Theory
- Handshake: Σ deg(v) = 2|E|
- Complete graph: |E| = n(n-1)/2
- Tree: |E| = |V| - 1

### Sequences
- Arithmetic sum: Sₙ = n(a₁+aₙ)/2
- Geometric sum: Sₙ = a₁(1-rⁿ)/(1-r)
- Geometric series: S = a₁/(1-r) for |r| < 1

---

## Practice Problem Types

### Set Theory
- Prove set equalities using double containment
- Find power sets and cardinalities
- Apply De Morgan's laws

### Functions
- Determine if function is injective/surjective/bijective
- Find compositions and inverses
- Count functions between finite sets

### Number Theory
- Use Euclidean algorithm for GCD
- Solve modular arithmetic problems
- Apply Fundamental Theorem of Arithmetic

### Combinatorics
- Count permutations and combinations
- Apply inclusion-exclusion principle
- Solve distribution problems with stars and bars

### Probability
- Calculate conditional probabilities
- Apply Bayes' theorem
- Find expected values and variances

### Graph Theory
- Determine if graphs are isomorphic
- Find Euler circuits/paths
- Analyze degree sequences

### Logic and Proofs
- Construct truth tables
- Prove statements using various techniques
- Identify valid argument forms

### Induction
- Prove summation formulas
- Prove divisibility statements
- Prove inequalities

### Complexity
- Analyze algorithm time complexity
- Apply Big-O notation
- Solve recurrence relations

---

**End of Advanced Review Notes**

*Good luck with your studies! Remember: practice is key to mastering discrete mathematics.*
