# 7.  Hierarchies

We have seen in [Chapter 6](C06_Structures.html#structures) how to define the class of groups and build instances of this class, and then how to build an instance of the commutative ring class. But of course there is a hierarchy here: a commutative ring is in particular an additive group. In this chapter we will study how to build such hierarchies. They appear in all branches of mathematics but in this chapter the emphasis will be on algebraic examples.

It may seem premature to discuss how to build hierarchies before more discussions about using existing hierarchies. But some understanding of the technology underlying hierarchies is required to use them. So you should probably still read this chapter, but without trying too hard to remember everything on your first read, then read the following chapters and come back here for a second reading.

In this chapter, we will redefine (simpler versions of) many things that appear in Mathlib so we will used indices to distinguish our version. For instance we will have `Ring₁` as our version of `Ring`. Since we will gradually explain more powerful ways of formalizing structures, those indices will sometimes grow beyond one.

## 7.1.  Basics

At the very bottom of all hierarchies in Lean, we find data-carrying classes. The following class records that the given type `α` is endowed with a distinguished element called `one`. At this stage, it has no property at all.

```
class One₁ (α : Type) where
  /-- The element one -/
  one : α
```

Since we’ll make a much heavier use of classes in this chapter, we need to understand some more details about what the `class` command is doing. First, the `class` command above defines a structure `One₁` with parameter `α : Type` and a single field `one`. It also mark this structure as a class so that arguments of type `One₁ α` for some type `α` will be inferrable using the instance resolution procedure, as long as they are marked as instance-implicit, ie appear between square brackets. Those two effects could also have been achieved using the `structure` command with `class` attribute, ie writing `@[class] structure` instance of `class`. But the class command also ensures that `One₁ α` appears as an instance-implicit argument in its own fields. Compare:

```
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one
```

In the second check, we can see that `self : One₂ α` is an explicit argument. Let us make sure the first version is indeed usable without any explicit argument.

```
example (α : Type) [One₁ α] : α := One₁.one
```

Remark: in the above example, the argument `One₁ α` is marked as instance-implicit, which is a bit silly since this affects only *uses* of the declaration and declaration created by the `example` command cannot be used. However it allows to avoid giving a name to that argument and, more importantly, it starts installing the good habit of marking `One₁ α` arguments as instance-implicit.

Another remark is that all this will work only when Lean knows what is `α`. In the above example, leaving out the type ascription `: α` would generate an error message like: `typeclass instance problem is stuck, it is often due to metavariables One₁ (?m.263 α)` where `?m.263 α` means “some type depending on `α`” (and 263 is simply an auto-generated index that would be useful to distinguish between several unknown things). Another way to avoid this issue would be to use a type annotation, as in:

```
example (α : Type) [One₁ α] := (One₁.one : α)
```

You may have already encountered that issue when playing with limits of sequences in [Section 3.6](C03_Logic.html#sequences-and-convergence) if you tried to state for instance that `0 < 1` without telling Lean whether you meant this inequality to be about natural numbers or real numbers.

Our next task is to assign a notation to `One₁.one`. Since we don’t want collisions with the builtin notation for `1`, we will use `𝟙`. This is achieved by the following command where the first line tells Lean to use the documentation of `One₁.one` as documentation for the symbol `𝟙`.

```
@[inherit\_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl
```

We now want a data-carrying class recording a binary operation. We don’t want to choose between addition and multiplication for now so we’ll use diamond.

```
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia
```

As in the `One₁` example, the operation has no property at all at this stage. Let us now define the class of semigroup structures where the operation is denoted by `⋄`. For now, we define it by hand as a structure with two fields, a `Dia₁` instance and some `Prop`-valued field `dia\_assoc` asserting associativity of `⋄`.

```
class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia\_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
```

Note that while stating dia\_assoc, the previously defined field toDia₁ is in the local context hence can be used when Lean searches for an instance of Dia₁ α to make sense of a ⋄ b. However this toDia₁ field does not become part of the type class instances database. Hence doing `example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b` would fail with error message `failed to synthesize instance Dia₁ α`.

We can fix this by adding the `instance` attribute later.

```
attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b
```

Before building up, we need a more convenient way to extend structures than explicitly writing fields like toDia₁ and adding the instance attribute by hand. The `class` supports this using the `extends` syntax as in:

```
class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia\_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b
```

Note this syntax is also available in the `structure` command, although it that case it fixes only the hurdle of writing fields such as toDia₁ since there is no instance to define in that case.

Let us now try to combine a diamond operation and a distinguished one with axioms saying this element is neutral on both sides.

```
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one\_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia\_one : ∀ a : α, a ⋄ 𝟙 = a
```

In the next example, we tell Lean that `α` has a `DiaOneClass₁` structure and state a property that uses both a Dia₁ instance and a One₁ instance. In order to see how Lean finds those instances we set a tracing option whose result can be seen in the info view. This result is rather terse by default but can be expended by clicking one lines ending with black arrows. It includes failed attempts where Lean tried to find instances before having enough type information to succeed. The successful attempts do involve the instances generated by the `extends` syntax.

```
set\_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙
```

Note that we don’t need to include extra fields where combining existing classes. Hence we can define monoids as:

```
class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α
```

While the above definition seems straightforward, it hides an important subtlety. Both `Semigroup₁ α` and `DiaOneClass₁ α` extend `Dia₁ α`, so one could fear that having a `Monoid₁ α` instance gives two unrelated diamond operations on `α`, one coming from a field `Monoid₁.toSemigroup₁` and one coming from a field `Monoid₁.toDiaOneClass₁`.

Indeed if we try to build a monoid class by hand using:

```
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α
```

then we get two completely unrelated diamond operations `Monoid₂.toSemigroup₁.toDia₁.dia` and `Monoid₂.toDiaOneClass₁.toDia₁.dia`.

The version generated using the `extends` syntax does not have this defect.

```
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl
```

So the `class` command did some magic for us (and the `structure` command would have done it too). An easy way to see what are the fields of our classes is to check their constructor. Compare:

```
/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one\_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia\_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk
```

So we see that `Monoid₁` takes `Semigroup₁ α` argument as expected but then it won’t take a would-be overlapping `DiaOneClass₁ α` argument but instead tears it apart and includes only the non-overlapping parts. And it also auto-generated an instance `Monoid₁.toDiaOneClass₁` which is *not* a field but has the expected signature which, from the end-user point of view, restores the symmetry between the two extended classes `Semigroup₁` and `DiaOneClass₁`.

```
#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁
```

We are now very close to defining groups. We could add to the monoid structure a field asserting the existence of an inverse for every element. But then we would need to work to access these inverses. In practice it is more convenient to add it as data. To optimize reusability, we define a new data-carrying class, and then give it some notation.

```
class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit\_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv G where
  inv\_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
```

The above definition may seem too weak, we only ask that `a⁻¹` is a left-inverse of `a`. But the other side is automatic. In order to prove that, we need a preliminary lemma.

```
lemma left\_inv\_eq\_right\_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one\_dia c, ← hba, Semigroup₁.dia\_assoc, hac, DiaOneClass₁.dia\_one b]
```

In this lemma, it is pretty annoying to give full names, especially since it requires knowing which part of the hierarchy provides those facts. One way to fix this is to use the `export` command to copy those facts as lemmas in the root name space.

```
export DiaOneClass₁ (one\_dia dia\_one)
export Semigroup₁ (dia\_assoc)
export Group₁ (inv\_dia)
```

We can then rewrite the above proof as:

```
example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one\_dia c, ← hba, dia\_assoc, hac, dia\_one b]
```

It is now your turn to prove things about our algebraic structures.

```
lemma inv\_eq\_of\_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
  sorry

lemma dia\_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
  sorry
```

At this stage we would like to move on to define rings, but there is a serious issue. A ring structure on a type contains both an additive group structure and a multiplicative monoid structure, and some properties about their interaction. But so far we hard-coded a notation `⋄` for all our operations. More fundamentally, the type class system assumes every type has only one instance of each type class. There are various ways to solve this issue. Surprisingly Mathlib uses the naive idea to duplicate everything for additive and multiplicative theories with the help of some code-generating attribute. Structures and classes are defined in both additive and multiplicative notation with an attribute `to\_additive` linking them. In case of multiple inheritance like for semi-groups, the auto-generated “symmetry-restoring” instances need also to be marked. This is a bit technical; you don’t need to understand details. The important point is that lemmas are then only stated in multiplicative notation and marked with the attribute `to\_additive` to generate the additive version as `left\_inv\_eq\_right\_inv'` with its auto-generated additive version `left\_neg\_eq\_right\_neg'`. In order to check the name of this additive version we used the `whatsnew in` command on top of `left\_inv\_eq\_right\_inv'`.

```
class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add\_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to\_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul\_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to\_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to\_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul\_assoc₃)
export AddSemigroup₃ (add\_assoc₃)

whatsnew in
@[to\_additive]
lemma left\_inv\_eq\_right\_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one\_mul c, ← hba, mul\_assoc₃, hac, mul\_one b]

#check left\_neg\_eq\_right\_neg'
```

Equipped with this technology, we can easily define also commutative semigroups, monoids and groups, and then define rings.

```
class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add\_comm : ∀ a b : α, a + b = b + a

@[to\_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul\_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to\_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg\_add : ∀ a : G, -a + a = 0

@[to\_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv\_mul : ∀ a : G, a⁻¹ * a = 1
```

We should remember to tag lemmas with `simp` when appropriate.

```
attribute [simp] Group₃.inv\_mul AddGroup₃.neg\_add
```

Then we need to repeat ourselves a bit since we switch to standard notations, but at least `to\_additive` does the work of translating from the multiplicative notation to the additive one.

```
@[to\_additive]
lemma inv\_eq\_of\_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  sorry
```

Note that `to\_additive` can be asked to tag a lemma with `simp` and propagate that attribute to the additive version as follows.

```
@[to\_additive (attr := simp)]
lemma Group₃.mul\_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  sorry

@[to\_additive]
lemma mul\_left\_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  sorry

@[to\_additive]
lemma mul\_right\_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  sorry

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to\_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G
```

We are now ready for rings. For demonstration purposes we won’t assume that addition is commutative, and then immediately provide an instance of `AddCommGroup₃`. Mathlib does not play this game, first because in practice this does not make any ring instance easier and also because Mathlib’s algebraic hierarchy goes through semirings which are like rings but without opposites so that the proof below does not work for them. What we gain here, besides a nice exercise if you have never seen it, is an example of building an instance using the syntax that allows to provide a parent structure and some extra fields.

```
class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left\_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right\_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add\_comm := by
    sorry }
```

Of course we can also build concrete instances, such as a ring structure on integers (of course the instance below uses that all the work is already done in Mathlib).

```
instance : Ring₃ ℤ where
  add := (· + ·)
  add\_assoc₃ := add\_assoc
  zero := 0
  zero\_add := by simp
  add\_zero := by simp
  neg := (- ·)
  neg\_add := by simp
  mul := (· * ·)
  mul\_assoc₃ := mul\_assoc
  one := 1
  one\_mul := by simp
  mul\_one := by simp
  zero\_mul := by simp
  mul\_zero := by simp
  left\_distrib := Int.mul\_add
  right\_distrib := Int.add\_mul
```

As an exercise you can now set up a simple hierarchy for order relations, including a class for ordered commutative monoids, which have both a partial order and a commutative monoid structure such that `∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b`. Of course you need to add fields and maybe `extends` clauses to the following classes.

```
class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit\_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type)

class PartialOrder₁ (α : Type)

class OrderedCommMonoid₁ (α : Type)

instance : OrderedCommMonoid₁ ℕ where
```

We now want to discuss algebraic structures involving several types. The prime example is modules over rings. If you don’t know what is a module, you can pretend it means vector space and think that all our rings are fields. Those structures are commutative additive groups equipped with a scalar multiplication by elements of some ring.

We first define the data-carrying type class of scalar multiplication by some type `α` on some type `β`, and give it a right associative notation.

```
class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul
```

Then we can define modules (again think about vector spaces if you don’t know what is a module).

```
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero\_smul : ∀ m : M, (0 : R) • m = 0
  one\_smul : ∀ m : M, (1 : R) • m = m
  mul\_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add\_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul\_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n
```

There is something interesting going on here. While it isn’t too surprising that the ring structure on `R` is a parameter in this definition, you probably expected `AddCommGroup₃ M` to be part of the `extends` clause just as `SMul₃ R M` is. Trying to do that would lead to a mysterious sounding error message: `cannot find synthesization order for instance Module₁.toAddCommGroup₃ with type (R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M all remaining arguments have metavariables: Ring₃ ?R @Module₁ ?R ?inst✝ M`. In order to understand this message, you need to remember that such an `extends` clause would lead to a field `Module₃.toAddCommGroup₃` marked as an instance. This instance would have the signature appearing in the error message: `(R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M`. With such an instance in the type class database, each time Lean would look for a `AddCommGroup₃ M` instance for some `M`, it would need to go hunting for a completely unspecified type `R` and a `Ring₃ R` instance before embarking on the main quest of finding a `Module₁ R M` instance. Those two side-quests are represented by the meta-variables mentioned in the error message and denoted by `?R` and `?inst✝` there. Such a `Module₃.toAddCommGroup₃` instance would then be a huge trap for the instance resolution procedure and then `class` command refuses to set it up.

What about `extends SMul₃ R M` then? That one creates a field `Module₁.toSMul₃ : {R : Type} →  [inst : Ring₃ R] → {M : Type} → [inst\_1 : AddCommGroup₃ M] → [self : Module₁ R M] → SMul₃ R M` whose end result `SMul₃ R M` mentions both `R` and `M` so this field can safely be used as an instance. The rule is easy to remember: each class appearing in the `extends` clause should mention every type appearing in the parameters.

Let us create our first module instance: a ring is a module over itself using its multiplication as a scalar multiplication.

```
instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero\_smul := zero\_mul
  one\_smul := one\_mul
  mul\_smul := mul\_assoc₃
  add\_smul := Ring₃.right\_distrib
  smul\_add := Ring₃.left\_distrib
```

As a second example, every abelian group is a module over `ℤ` (this is one of the reason to generalize the theory of vector spaces by allowing non-invertible scalars). First one can define scalar multiplication by a natural number for any type equipped with a zero and an addition: `n • a` is defined as `a + ⋯ + a` where `a` appears `n` times. Then this is extended to scalar multiplication by an integer by ensuring `(-1) • a = -a`.

```
def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, \_ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a
```

Proving this gives rise to a module structure is a bit tedious and not interesting for the current discussion, so we will sorry all axioms. You are *not* asked to replace those sorries with proofs. If you insist on doing it then you will probably want to state and prove several intermediate lemmas about `nsmul₁` and `zsmul₁`.

```
instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero\_smul := sorry
  one\_smul := sorry
  mul\_smul := sorry
  add\_smul := sorry
  smul\_add := sorry
```

A much more important issue is that we now have two module structures over the ring `ℤ` for `ℤ` itself: `abGrpModule ℤ` since `ℤ` is a abelian group, and `selfModule ℤ` since `ℤ` is a ring. Those two module structure correspond to the same abelian group structure, but it is not obvious that they have the same scalar multiplication. They actually do, but this isn’t true by definition, it requires a proof. This is very bad news for the type class instance resolution procedure and will lead to very frustrating failures for users of this hierarchy. When directly asked to find an instance, Lean will pick one, and we can see which one using:

```
#synth Module₁ ℤ ℤ -- abGrpModule ℤ
```

But in a more indirect context it can happen that Lean infers the one and then gets confused. This situation is known as a bad diamond. This has nothing to do with the diamond operation we used above, it refers to the way one can draw the paths from `ℤ` to its `Module₁ ℤ` going through either `AddCommGroup₃ ℤ` or `Ring₃ ℤ`.

It is important to understand that not all diamonds are bad. In fact there are diamonds everywhere in Mathlib, and also in this chapter. Already at the very beginning we saw one can go from `Monoid₁ α` to `Dia₁ α` through either `Semigroup₁ α` or `DiaOneClass₁ α` and thanks to the work done by the `class` command, the resulting two `Dia₁ α` instances are definitionally equal. In particular a diamond having a `Prop`-valued class at the bottom cannot be bad since any too proofs of the same statement are definitionally equal.

But the diamond we created with modules is definitely bad. The offending piece is the `smul` field which is data, not a proof, and we have two constructions that are not definitionally equal. The robust way of fixing this issue is to make sure that going from a rich structure to a poor structure is always done by forgetting data, not by defining data. This well-known pattern as been named “forgetful inheritance” and extensively discussed in <https://inria.hal.science/hal-02463336>.

In our concrete case, we can modify the definition of `AddMonoid₃` to include a `nsmul` data field and some `Prop`-valued fields ensuring this operation is provably the one we constructed above. Those fields are given default values using `:=` after their type in the definition below. Thanks to these default values, most instances would be constructed exactly as with our previous definitions. But in the special case of `ℤ` we will be able to provide specific values.

```
class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul\_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul\_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩
```

Let us check we can still construct a product monoid instance without providing the `nsmul` related fields.

```
instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add\_assoc₃ := fun a b c ↦ by ext <;> apply add\_assoc₃
  zero := (0, 0)
  zero\_add := fun a ↦ by ext <;> apply zero\_add
  add\_zero := fun a ↦ by ext <;> apply add\_zero
```

And now let us handle the special case of `ℤ` where we want to build `nsmul` using the coercion of `ℕ` to `ℤ` and the multiplication on `ℤ`. Note in particular how the proof fields contain more work than in the default value above.

```
instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add\_assoc₃ := Int.add\_assoc
  zero := 0
  zero\_add := Int.zero\_add
  add\_zero := Int.add\_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul\_zero := Int.zero\_mul
  nsmul\_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add\_mul, Int.add\_comm, Int.one\_mul]
```

Let us check we solved our issue. Because Lean already has a definition of scalar multiplication of a natural number and an integer, and we want to make sure our instance is used, we won’t use the `•` notation but call `SMul.mul` and explicitly provide our instance defined above.

```
example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
```

This story then continues with incorporating a `zsmul` field into the definition of groups and similar tricks. You are now ready to read the definition of monoids, groups, rings and modules in Mathlib. There are more complicated than what we have seen here, because they are part of a huge hierarchy, but all principles have been explained above.

As an exercise, you can come back to the order relation hierarchy you built above and try to incorporate a type class `LT₁` carrying the Less-Than notation `<₁` and make sure that every preorder comes with a `<₁` which has a default value built from `≤₁` and a `Prop`-valued field asserting the natural relation between those two comparison operators. -/

## 7.2.  Morphisms

So far in this chapter, we discussed how to create a hierarchy of mathematical structures. But defining structures is not really completed until we have morphisms. There are two main approaches here. The most obvious one is to define a predicate on functions.

```
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
```

In this definition, it is a bit unpleasant to use a conjunction. In particular users will need to remember the ordering we chose when they want to access the two conditions. So we could use a structure instead.

```
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map\_one : f 1 = 1
  map\_mul : ∀ g g', f (g * g') = f g * f g'
```

Once we are here, it is even tempting to make it a class and use the type class instance resolution procedure to automatically infer `isMonoidHom₂` for complicated functions out of instances for simpler functions. For instance a composition of monoid morphisms is a monoid morphism and this seems like a useful instance. However such an instance would be very tricky for the resolution procedure since it would need to hunt down `g ∘ f` everywhere. Seeing it failing in `g (f x)` would be very frustrating. More generally one must always keep in mind that recognizing which function is applied in a given expression is a very difficult problem, called the “higher-order unification problem”. So Mathlib does not use this class approach.

A more fundamental question is whether we use predicates as above (using either a `def` or a `structure`) or use structures bundling a function and predicates. This is partly a psychological issue. It is extremely rare to consider a function between monoids that is not a morphism. It really feels like “monoid morphism” is not an adjective you can assign to a bare function, it is a noun. On the other hand one can argue that a continuous function between topological spaces is really a function that happens to be continuous. This is one reason why Mathlib has a `Continuous` predicate. For instance you can write:

```
example : Continuous (id : ℝ → ℝ) := continuous\_id
```

We still have bundles continuous functions, which are convenient for instance to put a topology on a space of continuous functions, but they are not the primary tool to work with continuity.

By contrast, morphisms between monoids (or other algebraic structures) are bundled as in:

```
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map\_one : toFun 1 = 1
  map\_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'
```

Of course we don’t want to type `toFun` everywhere so we register a coercion using the `CoeFun` type class. Its first argument is the type we want to coerce to a function. The second argument describes the target function type. In our case it is always `G → H` for every `f : MonoidHom₁ G H`. We also tag `MonoidHom₁.toFun` with the `coe` attribute to make sure it is displayed almost invisibly in the tactic state, simply by a `↑` prefix.

```
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun \_ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun
```

Let us check we can indeed apply a bundled monoid morphism to an element.

```
example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map\_one
```

We can do the same with other kind of morphisms until we reach ring morphisms.

```
@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map\_zero : toFun 0 = 0
  map\_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun \_ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S
```

There are a couple of issues about this approach. A minor one is we don’t quite know where to put the `coe` attribute since the `RingHom₁.toFun` does not exist, the relevant function is `MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁` which is not a declaration that can be tagged with an attribute (but we could still define a `CoeFun  (RingHom₁ R S) (fun \_ ↦ R → S)` instance). A much more important one is that lemmas about monoid morphisms won’t directly apply to ring morphisms. This leaves the alternative of either juggling with `RingHom₁.toMonoidHom₁` each time we want to apply a monoid morphism lemma or restate every such lemmas for ring morphisms. Neither option is appealing so Mathlib uses a new hierarchy trick here. The idea is to define a type class for objects that are at least monoid morphisms, instantiate that class with both monoid morphisms and ring morphisms and use it to state every lemma. In the definition below, `F` could be `MonoidHom₁ M N`, or `RingHom₁ M N` if `M` and `N` have a ring structure.

```
class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map\_one : ∀ f : F, toFun f 1 = 1
  map\_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'
```

However there is a problem with the above implementation. We haven’t registered a coercion to function instance yet. Let us try to do it now.

```
def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun \_ ↦ M → N) where
  coe := MonoidHomClass₁.toFun
```

Making the an instance would be bad. When faced with something like `f x` where the type of `f` is not a function type, Lean will try to find a `CoeFun` instance to coerce `f` into a function. The above function has type: `{M N F : Type} → [Monoid M] → [Monoid N] → [MonoidHomClass₁ F M N] → CoeFun F (fun x ↦ M → N)` so, when it trying to apply it, it wouldn’t be a priori clear to Lean in which order the unknown types `M`, `N` and `F` should be inferred. This is a kind of bad instance that is slightly different from the one we saw already, but it boils down to the same issue: without knowing `M`, Lean would have to search for a monoid instance on an unknown type, hence hopelessly try *every* monoid instance in the database. If you are curious to see the effect of such an instance you can type `set\_option synthInstance.checkSynthOrder false in` on top of the above declaration, replace `def badInst` with `instance`, and look for random failures in this file.

Here the solution is easy, we need to tell Lean to first search what is `F` and then deduce `M` and `N`. This is done using the `outParam` function. This function is defined as the identity function, but is still recognized by the type class machinery and triggers the desired behavior. Hence we can retry defining our class, paying attention to the `outParam` function:

```
class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map\_one : ∀ f : F, toFun f 1 = 1
  map\_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun \_ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun
```

Now we can proceed with our plan to instantiate this class.

```
instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map\_one := fun f ↦ f.map\_one
  map\_mul := fun f ↦ f.map\_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map\_one := fun f ↦ f.toMonoidHom₁.map\_one
  map\_mul := fun f ↦ f.toMonoidHom₁.map\_mul
```

As promised every lemma we prove about `f : F` assuming an instance of `MonoidHomClass₁ F` will apply both to monoid morphisms and ring morphisms. Let us see an example lemma and check it applies to both situations.

```
lemma map\_inv\_of\_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map\_mul, h, MonoidHomClass₂.map\_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map\_inv\_of\_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map\_inv\_of\_inv f h
```

At first sight, it may look like we got back to our old bad idea of making `MonoidHom₁` a class. But we haven’t. Everything is shifted one level of abstraction up. The type class resolution procedure won’t be looking for functions, it will be looking for either `MonoidHom₁` or `RingHom₁`.

One remaining issue with our approach is the presence of repetitive code around the `toFun` field and the corresponding `CoeFun` instance and `coe` attribute. It would also be better to record that this pattern is used only for function with extra properties, meaning that the coercion to functions should be injective. So Mathlib adds one more layer of abstraction with the base class `FunLike`. Let us redefine our `MonoidHomClass` on top of this base layer.

```
class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    FunLike F M (fun \_ ↦ N) where
  map\_one : ∀ f : F, f 1 = 1
  map\_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe\_injective' := MonoidHom₁.ext
  map\_one := MonoidHom₁.map\_one
  map\_mul := MonoidHom₁.map\_mul
```

Of course the hierarchy of morphisms does not stop here. We could go on and define a class `RingHomClass₃` extending `MonoidHomClass₃` and instantiate it on `RingHom` and then later on `AlgebraHom` (algebras are rings with some extra structure). But we’ve covered the main formalization ideas used in Mathlib for morphisms and you should be ready to understand how morphisms are defined in Mathlib.

As an exercise, you should try to define your class of bundled order-preserving function between ordered types, and then order preserving monoid morphisms. This is for training purposes only. Like continuous functions, order preserving functions are primarily unbundled in Mathlib where they are defined by the `Monotone` predicate. Of course you need to complete the class definitions below.

```
@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le\_of\_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

@[ext]
structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
MonoidHom₁ M N, OrderPresHom M N

class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]

instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    OrderPresHomClass (OrderPresMonoidHom α β) α β where

instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
    MonoidHomClass₃ (OrderPresMonoidHom α β) α β
  := sorry
```

## 7.3.  Sub-objects

After defining some algebraic structure and its morphisms, the next step is to consider sets that inherit this algebraic structure, for instance subgroups or subrings. This largely overlaps our previous topic. Indeed a set in `X` is implemented as a function from `X` to `Prop` so sub-objects are function satisfying a certain predicate. Hence we can reuse of lot of the ideas that led to the `FunLike` class and its descendants. We won’t reuse `FunLike` itself because this would break the abstraction barrier from `Set X` to `X → Prop`. Instead there is a `SetLike` class. Instead of wrapping an injection into a function type, that class wraps an injection into a `Set` type and defines the corresponding coercion and `Membership` instance.

```
@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul\_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one\_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe\_injective' := Submonoid₁.ext
```

Equipped with the above `SetLike` instance, we can already state naturally that a submonoid `N` contains `1` without using `N.carrier`. We can also silently treat `N` as a set in `M` as take its direct image under a map.

```
example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one\_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N
```

We also have a coercion to `Type` which uses `Subtype` so, given a submonoid `N` we can write a parameter `(x : N)` which can be coerced to an element of `M` belonging to `N`.

```
example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property
```

Using this coercion to `Type` we can also tackle the task of equipping a submonoid with a monoid structure. We will use the coercion from the type associated to `N` as above, and the lemma `SetCoe.ext` asserting this coercion is injective. Both are provided by the `SetLike` instance.

```
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul\_mem x.property y.property⟩
  mul\_assoc := fun x y z ↦ SetCoe.ext (mul\_assoc (x : M) y z)
  one := ⟨1, N.one\_mem⟩
  one\_mul := fun x ↦ SetCoe.ext (one\_mul (x : M))
  mul\_one := fun x ↦ SetCoe.ext (mul\_one (x : M))
```

Note that, in the above instance, instead of using the coercion to `M` and calling the `property` field, we could have used destructuring binders as follows.

```
example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul\_mem hx hy⟩
  mul\_assoc := fun ⟨x, \_⟩ ⟨y, \_⟩ ⟨z, \_⟩ ↦ SetCoe.ext (mul\_assoc x y z)
  one := ⟨1, N.one\_mem⟩
  one\_mul := fun ⟨x, \_⟩ ↦ SetCoe.ext (one\_mul x)
  mul\_one := fun ⟨x, \_⟩ ↦ SetCoe.ext (mul\_one x)
```

In order to apply lemmas about submonoids to subgroups or subrings, we need a class, just like for morphisms. Note this class take a `SetLike` instance as a parameter so it does not need a carrier field and can use the membership notation in its fields.

```
class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul\_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one\_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul\_mem := Submonoid₁.mul\_mem
  one\_mem := Submonoid₁.one\_mem
```

As an exercise you should define a `Subgroup₁` structure, endow it with a `SetLike` instance and a `SubmonoidClass₁` instance, put a `Group` instance on the subtype associated to a `Subgroup₁` and define a `SubgroupClass₁` class.

Another very important thing to know about subobjects of a given algebraic object in Mathlib always form a complete lattice, and this structure is used a lot. For instance you may look for the lemma saying that an intersection of submonoids is a submonoid. But this won’t be a lemma, this will be an infimum construction. Let us do the case of two submonoids.

```
instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one\_mem := ⟨S₁.one\_mem, S₂.one\_mem⟩
      mul\_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul\_mem hx hy, S₂.mul\_mem hx' hy'⟩ }⟩
```

This allows to get the intersections of two submonoids as a submonoid.

```
example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P
```

You may think it’s a shame that we had to use the inf symbol `⊓` in the above example instead of the intersection symbol `∩`. But think about the supremum. The union of two submonoids is not a submonoid. However submonoids still form a lattice (even a complete one). Actually `N ⊔ P` is the submonoid generated by the union of `N` and `P` and of course it would be very confusing to denote it by `N ∪ P`. So you can see the use of `N ⊓ P` as much more consistent. It is also a lot more consistent across various kind of algebraic structures. It may look a bit weird at first to see the sum of two vector subspace `E` and `F` denoted by `E ⊔ F` instead of `E + F`. But you will get used to it. And soon you will consider the `E + F` notation as a distraction emphasizing the anecdotal fact that elements of `E ⊔ F` can be written as a sum of an element of `E` and an element of `F` instead of emphasizing the fundamental fact that `E ⊔ F` is the smallest vector subspace containing both `E` and `F`.

Our last topic for this chapter is that of quotients. Again we want to explain how convenient notation are built and code duplication is avoided in Mathlib. Here the main device is the `HasQuotient` class which allows notations like `M ⧸ N`. Beware the quotient symbol `⧸` is a special unicode character, not a regular ASCII division symbol.

As an example, we will build the quotient of a commutative monoid by a submonoid, leave proofs to you. In the last example, you can use `Setoid.refl` but it won’t automatically pick up the relevant `Setoid` structure. You can fix this issue by providing all arguments using the `@` syntax, as in `@Setoid.refl M N.Setoid`.

```
def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one\_mem, 1, N.one\_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      sorry
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂' (· * ·) (by
      sorry
        )
  mul\_assoc := by
      sorry
  one := QuotientMonoid.mk N 1
  one\_mul := by
      sorry
  mul\_one := by
      sorry
```
