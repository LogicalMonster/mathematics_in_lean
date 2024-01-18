# 7.  Hierarchies

在[第六章](C06_Structures.md#6-Structures)中，我们已经看到如何定义群的类别并建立这个类别的实例，然后如何建立交换环类别的实例。然而，这里有一个层次结构：交换环本质上就是一个加法群。在本章中，我们将研究如何构建这样的层次结构。它们出现在所有的数学分支中，但在本章中，我们将主要关注代数示例。

在进一步讨论如何使用现有层次结构之前，讨论如何构建层次结构可能显得过于仓促。但要理解并使用层次结构，需要一定的基础技术知识。所以你可能还是应该阅读本章，但不需要强记所有内容，然后阅读接下来的章节，然后回到这里进行二次阅读。

在这一章，我们将重新定义在Mathlib中出现的许多事物的（更简洁的版本），因此我们将使用索引来区分我们的版本。例如，我们将有`Ring₁`作为我们版本的`Ring`。由于我们将逐步解释更强大的形式化结构的方法，这些索引有时会增加到一以上。

## 7.1.  Basics

在所有Lean层次结构的底部，我们都可以找到携带数据的类。以下类记录了给定类型`α`具有一个称为`one`的特殊元素。在这个阶段，它没有任何属性。

```
class One₁ (α : Type) where
  /-- The element one -/
  one : α
```

由于我们在这一章将大量使用类，因此我们需要更详细地了解`class`命令的执行情况。首先，`class`命令定义了一个带有参数`α : Type`和单一字段`one`的结构`One₁`。它还将该结构标记为类，因此只要它们被标记为实例隐含，即出现在方括号之间，`One₁ α`类型的参数就可以使用实例解析程序推断出来。这两种效果也可以通过使用带有`class`属性的`structure`命令实现，即写为`@[class] structure`而不是`class`。但是`class`命令也确保`One₁ α`作为实例隐含参数出现在其自身的字段中。对比：

```
#check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

@[class] structure One₂ (α : Type) where
  /-- The element one -/
  one : α

#check One₂.one
```

在第二次检查中，我们可以看到`self : One₂ α`是一个明确的参数。让我们确保第一种版本确实可以在不用任何明确参数的情况下使用。

```
example (α : Type) [One₁ α] : α := One₁.one
```

备注：在上例中，参数 `One₁ α` 被标记为实例隐含，这有点傻，因为这只影响声明的*使用情况*，`example` 命令创建的声明不能被使用。然而，它允许避免给该参数命名，并且更重要的是，它开始安装将 `One₁ α` 参数标记为实例隐含的好习惯。

另一个备注是，只有当 Lean 知道什么是 `α` 时，所有这些才会起作用。在上述例子中，不注明类型（`: α`）会产生错误信息，如：`类型类实例问题停滞不前，通常是由包含 `α` 的未知类型元变量造成的 One₁ (?m.263 α)`,其中 `?m.263 α` 指的是“基于 `α` 的一些类型（和 263 只是一个自动生成的索引，用于区分不同的未知事物）”。另一种避免这个问题的方法是使用类型注释，例如：

```
example (α : Type) [One₁ α] := (One₁.one : α)
```

如果你在[第3.6节](C03_Logic.md#36-Sequences-and-Convergence)中尝试做序列极限时，试图声明 `0 < 1` 而不告诉Lean你是在讨论自然数还是实数，则可能已经遇到过这个问题。

我们接下来的任务是给 `One₁.one` 赋予一个符号。由于我们不希望与 `1` 的内建符号发生冲突，我们将使用 `𝟙`。这可以通过下面的命令实现，其中第一行告诉Lean使用 `One₁.one` 的文档作为符号 `𝟙` 的文档。

```
@[inherit_doc]
notation "𝟙" => One₁.one

example {α : Type} [One₁ α] : α := 𝟙

example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl
```

我们现在想要一个记录二元运算的数据携带类。我们现在并不想选择加法和乘法，所以我们将使用菱形。

```
class Dia₁ (α : Type) where
  dia : α → α → α

infixl:70 " ⋄ "   => Dia₁.dia
```

在 `One₁` 的例子中，这个操作在这个阶段完全没有任何属性。现在让我们定义一个半群结构的类，其操作由 `⋄` 表示。现在，我们通过手动定义一个具有两个字段的结构来定义它，一个是 `Dia₁` 的实例，另一个是一些 `Prop` 值字段 `dia_assoc`，它断言了 `⋄` 的结合性。

```
class Semigroup₁ (α : Type) where
  toDia₁ : Dia₁ α
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)
```

注意，在声明 dia_assoc 时，先前定义的字段 toDia₁ 是在本地上下文中的，因此可以在 Lean 搜索 Dia₁ α 的实例以找到 a ⋄ b 时使用。然而，这个 toDia₁ 字段并没有成为类型类实例数据库的一部分。因此，执行 `example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b` 将失败，错误信息为`无法合成实例 Dia₁ α`。

我们可以通过稍后添加 `instance` 属性来修复这个问题。

```
attribute [instance] Semigroup₁.toDia₁

example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b
```

在构建之前，我们需要一种比如明确写出像toDia₁这样的字段和手动添加实例属性的方式来扩展结构的更方便的方法。`class`支持通过`extends`语法实现，例如：

```
class Semigroup₂ (α : Type) extends Dia₁ α where
  /-- Diamond is associative -/
  dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

example {α : Type} [Semigroup₂ α] (a b : α) : α := a ⋄ b
```

注意这个语法也在`structure`命令中可用，尽管在这种情况下，它只解决了写成如toDia₁这样的字段的难题，因为在那种情况下没有实例要定义。

我们现在试图结合一个钻石操作和一个突出的操作，用公理说明这个元素在两边都是中性的。

```
class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
  /-- One is a left neutral element for diamond. -/
  one_dia : ∀ a : α, 𝟙 ⋄ a = a
  /-- One is a right neutral element for diamond -/
  dia_one : ∀ a : α, a ⋄ 𝟙 = a
```

在下一个例子中，我们告诉 Lean `α`有一个`DiaOneClass₁`结构，并声明一个使用Dia₁实例和One₁实例的属性。为了看到 Lean 如何找到这些实例，我们设置了一个 tracing 选项，其结果可以在info视图中看到。这个结果默认是相当简洁的，但可以通过点击结束与黑箭头的线条进行扩展。它包括失败的尝试，其中 Lean 在有足够的类型信息才能成功之前尝试去找实例。成功的尝试确实涉及到由`extends`语法生成的实例。

```
set_option trace.Meta.synthInstance true in
example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙
```

注意，我们不需要在组合现有类时包含额外的字段。因此我们可以定义单词如下：

```
class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α
```

虽然上面的定义看起来很直接，但它隐藏了一个重要的细微差别。`Semigroup₁ α`和`DiaOneClass₁ α`都扩展了`Dia₁ α`，所以人们可能会担心，有一个`Monoid₁ α`实例会在`α`上给出两个无关的钻石操作，一个来自字段`Monoid₁.toSemigroup₁`，一个来自字段`Monoid₁.toDiaOneClass₁`。

事实上，如果我们尝试使用以下方法手动构建一个 monoid 类：

```
class Monoid₂ (α : Type) where
  toSemigroup₁ : Semigroup₁ α
  toDiaOneClass₁ : DiaOneClass₁ α
```

然后我们得到了两个完全无关的钻石操作`Monoid₂.toSemigroup₁.toDia₁.dia`和`Monoid₂.toDiaOneClass₁.toDia₁.dia`。

使用`extends`语法生成的版本没有这个缺陷。

```
example {α : Type} [Monoid₁ α] :
  (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl
```

所以`class`命令为我们做了一些魔术（`structure`命令也会这样做）。查看它们的构造函数是了解我们的类的字段的一种简单方法。比较：

```
/- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
#check Monoid₂.mk

/- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
#check Monoid₁.mk
```

所以我们看到`Monoid₁`如我们所料地接受`Semigroup₁ α`参数，但然后它不会接受即将重叠的`DiaOneClass₁ α`参数，而是将它拆开并只包含非重叠的部分。而且它还自动生成了一个实例`Monoid₁.toDiaOneClass₁`，它并*不是*一个字段，但具有预期的签名，从最终用户的角度来看，恢复了两个扩展的类`Semigroup₁`和`DiaOneClass₁`之间的对称性。

```
#check Monoid₁.toSemigroup₁
#check Monoid₁.toDiaOneClass₁
```

我们现在已经非常接近定义群了。我们可以向 monoid 结构添加一个字段，断言每个元素存在一个逆元。但是然后我们需要努力访问这些逆元。事实上，将其作为数据添加更为方便。为了优化可重用性，我们定义一个新携带数据的类，然后给它一些符号。

```
class Inv₁ (α : Type) where
  /-- The inversion function -/
  inv : α → α

@[inherit_doc]
postfix:max "⁻¹" => Inv₁.inv

class Group₁ (G : Type) extends Monoid₁ G, Inv G where
  inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙
```

上述定义可能看起来过于弱，我们只要求 `a⁻¹` 是 `a`的左逆元。但另一边是自动的。为了证明这一点，我们需要一个初步的引理。

```
lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]
```

在这个引理中，给出全名是非常烦人的，尤其是需要知道哪部分的层次结构提供了这些事实。解决这个问题的一种方法是使用`export`命令将这些事实作为根名称空间中的引理进行复制。

```
export DiaOneClass₁ (one_dia dia_one)
export Semigroup₁ (dia_assoc)
export Group₁ (inv_dia)
```

我们可以将上述证明重写为：

```
example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
  rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]
```

现在轮到你来证明我们的代数结构的相关事宜。

```
lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
  sorry

lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
  sorry
```

在这个阶段，我们希望继续定义环，但存在一个严重的问题。一个类型的环结构包含一个加法群结构和一个乘法幺半群结构，以及它们之间的一些属性。但到目前为止，我们为所有的操作硬编码了一个符号 `⋄`。更基本地，类型类系统假设每个类型只有每个类型类的一个实例。有各种各样的方法可以解决这个问题。令人惊讶的是，Mathlib使用了一个简单的想法来为加法和乘法理论复制所有东西，它们用一些生成代码的属性来实现。结构和类在加法和乘法记号中都有定义，有一个属性 `to_additive` 将它们链接起来。在半群的多重继承的情况下，也需要标记自动生成的"对称恢复"实例。这有点技术性；你不需要理解细节。重要的一点是，引理只在乘法记号中陈述并用属性 `to_additive` 标记，生成加法版本作为 `left_inv_eq_right_inv'`，其自动生成的加法版本为 `left_neg_eq_right_neg'`。为了检查这个加法版本的名字，我们在 `left_inv_eq_right_inv'` 的顶部使用了 `whatsnew in` 命令。

```
class AddSemigroup₃ (α : Type) extends Add α where
/-- Addition is associative -/
  add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

@[to_additive AddSemigroup₃]
class Semigroup₃ (α : Type) extends Mul α where
/-- Multiplication is associative -/
  mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

@[to_additive AddMonoid₃]
class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

attribute [to_additive existing] Monoid₃.toMulOneClass

export Semigroup₃ (mul_assoc₃)
export AddSemigroup₃ (add_assoc₃)

whatsnew in
@[to_additive]
lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
  rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

#check left_neg_eq_right_neg'
```

有了这项技术，我们可以轻松地定义交换半群、幺半群和群，然后定义环。

```
class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
  add_comm : ∀ a b : α, a + b = b + a

@[to_additive AddCommSemigroup₃]
class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
  mul_comm : ∀ a b : α, a * b = b * a

class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

@[to_additive AddCommMonoid₃]
class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
  neg_add : ∀ a : G, -a + a = 0

@[to_additive AddGroup₃]
class Group₃ (G : Type) extends Monoid₃ G, Inv G where
  inv_mul : ∀ a : G, a⁻¹ * a = 1
```

我们应当记住在适当的时候为引理标记 `simp`。

```
attribute [simp] Group₃.inv_mul AddGroup₃.neg_add
```

然后我们需要重复我们自己一些，因为我们切换到标准记号，但至少 `to_additive` 做了从乘法记号转换到加法记号的工作。

```
@[to_additive]
lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
  sorry
```

注意，`to_additive` 可以被要求为引理标记 `simp` 并将该属性传播到加法版本，如下所示。

```
@[to_additive (attr := simp)]
lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
  sorry

@[to_additive]
lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
  sorry

@[to_additive]
lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
  sorry

class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

@[to_additive AddCommGroup₃]
class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G
```

我们现在准备开始研究环。出于演示目的，我们不会假设加法是可交换的，然后即刻提供一个 `AddCommGroup₃` 的实例。Mathlib 不会玩这个游戏，首先因为在实践中这不会让任何环实例更容易，同时因为 Mathlib 的代数层次结构经过 semirings，这些 semirings 就像没有反对立的环，所以下面的证明不适用于它们。除了一个很好的练习（如果你从未见过它）我们在这里获得的是，使用允许提供父结构和一些额外字段的语法建立实例的示例。

```
class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
  /-- Multiplication is left distributive over addition -/
  left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
  /-- Multiplication is right distributive over addition -/
  right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
{ Ring₃.toAddGroup₃ with
  add_comm := by
    sorry }
```

当然，我们也可以构建具体的实例，比如整数的环结构（当然下面的实例使用了在 Mathlib 中已经完成的所有工作）。

```
instance : Ring₃ ℤ where
  add := (· + ·)
  add_assoc₃ := add_assoc
  zero := 0
  zero_add := by simp
  add_zero := by simp
  neg := (- ·)
  neg_add := by simp
  mul := (· * ·)
  mul_assoc₃ := mul_assoc
  one := 1
  one_mul := by simp
  mul_one := by simp
  zero_mul := by simp
  mul_zero := by simp
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
```

作为一个练习，你现在可以为顺序关系设置一个简单的层级，包括一个有序的可交换幺半群的类，它们具有一个偏序和一个可交换幺半群的结构，使得 `∀ a b : α, a ≤ b → ∀ c : α, c * a ≤ c * b`。当然，你需要添加字段并可能为下面的类添加 `extends` 条款。

```
class LE₁ (α : Type) where
  /-- The Less-or-Equal relation. -/
  le : α → α → Prop

@[inherit_doc] infix:50 " ≤₁ " => LE₁.le

class Preorder₁ (α : Type)

class PartialOrder₁ (α : Type)

class OrderedCommMonoid₁ (α : Type)

instance : OrderedCommMonoid₁ ℕ where
```

现在，我们想讨论涉及多种类型的代数结构。最主要的例子是环上的模。如果你不知道什么是模，你可以假装它指的是向量空间，并认为我们所说的所有环都是字段。这些结构是配备了一些环元素的标量乘法的交换加法群。

我们首先定义标量乘法的数据携带型类，在某种类型 `α` 上对某种类型 `β`，并给它一个右关联记法。

```
class SMul₃ (α : Type) (β : Type) where
  /-- Scalar multiplication -/
  smul : α → β → β

infixr:73 " • " => SMul₃.smul
```

然后我们可以定义模（如果你不知道什么是模，就再次想到向量空间）。

```
class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
  zero_smul : ∀ m : M, (0 : R) • m = 0
  one_smul : ∀ m : M, (1 : R) • m = m
  mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
  add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
  smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n
```

这里有一些有趣的地方。虽然 `R` 上的环结构在这个定义中是一个参数并不奇怪，你可能预期 `AddCommGroup₃ M` 应该是 `extends` 子句的一部分，就像 `SMul₃ R M` 一样。试图这样做会导致一个神秘的错误消息：`cannot find synthesization order for instance Module₁.toAddCommGroup₃ with type (R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M all remaining arguments have metavariables: Ring₃ ?R @Module₁ ?R ?inst✝ M`。为了理解这条信息，你需要记住，这样的一个 `extends` 子句将导致一个字段 `Module₃.toAddCommGroup₃` 被标记为一个实例。这个实例将会有一个在错误消息中出现的签名：`(R : Type) → [inst : Ring₃ R] → {M : Type} → [self : Module₁ R M] → AddCommGroup₃ M`。有了这样一个实例在类型类数据库中，每当 Lean 需要寻找某个 `M` 的 `AddCommGroup₃ M` 实例时，它需要先寻找一个完全未指定的类型 `R` 以及一个 `Ring₃ R` 实例，然后再开始主要的任务，寻找一个 `Module₁ R M` 实例。这两个侧任务由错误消息中提到的元变量所代表，分别用 `?R` 和 `?inst✝` 表示。这样的一个 `Module₃.toAddCommGroup₃` 实例将会对实例解析程序构成一个巨大的陷阱，因此 `class` 命令拒绝设置它。

那么 `extends SMul₃ R M` 呢？那个创建了一个字段 `Module₁.toSMul₃ : {R : Type} →  [inst : Ring₃ R] → {M : Type} → [inst_1 : AddCommGroup₃ M] → [self : Module₁ R M] → SMul₃ R M` 其最终结果 `SMul₃ R M` 提到了 `R` 和 `M`，所以这个字段可以安全地用作实例。规则很容易记：在 `extends` 子句中出现的每个类都应提到参数中出现的每个类型。

让我们创建我们的第一个模实例：环是自己的模，用它的乘法作为标量乘法。

```
instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
  smul := fun r s ↦ r*s
  zero_smul := zero_mul
  one_smul := one_mul
  mul_smul := mul_assoc₃
  add_smul := Ring₃.right_distrib
  smul_add := Ring₃.left_distrib
```

作为第二个例子，每一个阿贝尔群都是 `ℤ` 上的模（这正是通过允许非可逆标量来推广向量空间理论的原因之一）。首先，对于任何配备了零和加法的类型，我们可以定义自然数的标量乘法：`n • a` 定义为 `a + ⋯ + a`，其中`a`出现`n`次。然后这个被扩展到整数上的标量乘法，通过确保 `(-1) • a = -a`。

```
def nsmul₁ [Zero M] [Add M] : ℕ → M → M
  | 0, _ => 0
  | n + 1, a => a + nsmul₁ n a

def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
  | Int.ofNat n, a => nsmul₁ n a
  | Int.negSucc n, a => -nsmul₁ n.succ a
```

证明这给出一个模结构是有点繁琐的，而且对于当前的讨论并不感兴趣，所以我们将对所有公理表示抱歉。你没有被要求将这些抱歉替换为证据。如果你坚持这样做，你可能需要陈述并证明关于 `nsmul₁` 和 `zsmul₁` 的几个中间引理。

```
instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
  smul := zsmul₁
  zero_smul := sorry
  one_smul := sorry
  mul_smul := sorry
  add_smul := sorry
  smul_add := sorry
```

一个更重要的问题是，我们现在有两种模块结构在环`ℤ`上对`ℤ`本身。：`abGrpModule ℤ`，因为`ℤ`是一个阿贝尔群，和 `selfModule ℤ`，因为 `ℤ` 是一个环。这两种模块结构对应于相同的阿贝尔群结构，但他们是否有相同的标量乘法并不明显。它们实际上是有的，但这并不是定义就确定的，需要证明。这对类型类的实例解析过程来说是个非常糟糕的消息，会导致使用该层次结构的用户遇到非常令人沮丧的失败。当直接要求找到一个实例时，Lean会选取一个，我们可以使用以下命令查看选取的是哪一个：

```
#synth Module₁ ℤ ℤ -- abGrpModule ℤ
```

但在更间接的上下文中，可能会发生Lean推断出了其中一个然后产生混淆的情况。这种情况被称为糟糕的钻石。这与我们之前所用的钻石操作没有任何关系，它指的是可以从`ℤ`绘制路径到它的`Module₁ ℤ`，通过 `AddCommGroup₃ ℤ`或 `Ring₃ ℤ`。

重要的是要理解并非所有的钻石都是糟糕的。事实上，Mathlib和本章中随处可见钻石。我们一开始就看到可以从`Monoid₁ α`到`Dia₁ α`，通过`Semigroup₁ α`或`DiaOneClass₁ α`，并且得益于`class`命令的工作，产生的两个`Dia₁ α`实例在概念上是相等的。特别地，如果一个钻石在底部有一个`Prop`-valued类，那么它就不可能是糟糕的，因为任何两个对同一语句的证明在概念上都是相等的。

但我们用模块创建的钻石确实是糟糕的。造成问题的是 `smul` 字段，它是数据，而不是证明，我们有两个构造不在定义上相等的方法。解决这个问题的稳健方式是确保从丰富的结构到贫穷的结构总是通过忘记数据，而不是定义数据。这个众所周知的模式被命名为“遗忘继承”，并在<https://inria.hal.science/hal-02463336>中进行了深入的讨论。

在我们的具体案例中，我们可以修改`AddMonoid₃`的定义, 包括一个`nsmul`数据字段和一些`Prop`-valued字段确保这个操作能被证明是我们上面构建的那个。这些字段在下面的定义中使用 `:=` 在他们的类型后面赋予默认值。多亏了这些默认值，大多数实例将像我们之前的定义那样构造。但在`ℤ`的特殊情况下，我们将能够提供特定的值。

```
class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
  /-- Multiplication by a natural number. -/
  nsmul : ℕ → M → M := nsmul₁
  /-- Multiplication by `(0 : ℕ)` gives `0`. -/
  nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
  /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
  nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩
```

让我们检查我们是否还可以构造一个不需要提供与`nsmul`相关字段的乘积幺半群实例。

```
instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
  add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
  add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
  zero := (0, 0)
  zero_add := fun a ↦ by ext <;> apply zero_add
  add_zero := fun a ↦ by ext <;> apply add_zero
```

现在让我们处理`ℤ`的特殊情况，我们希望用`ℕ`向`ℤ`的转换和`ℤ`上的乘法来构建`nsmul`。尤其注意到，与上面的默认值相比，证明字段包含更多的工作。

```
instance : AddMonoid₄ ℤ where
  add := (· + ·)
  add_assoc₃ := Int.add_assoc
  zero := 0
  zero_add := Int.zero_add
  add_zero := Int.add_zero
  nsmul := fun n m ↦ (n : ℤ) * m
  nsmul_zero := Int.zero_mul
  nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
    by rw [Int.add_mul, Int.add_comm, Int.one_mul]
```

我们来检查我们是否解决了问题。因为 Lean 已经有了一个定义，它描述了一个自然数和一个整数的标量乘法，我们想确保我们的实例被使用，所以我们不会使用 `•` 符号，而是调用 `SMul.mul` 并显式地提供我们上面定义的实例。

```
example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl
```

然后，这个故事又继续，包含了在群的定义中加入一个`zsmul`字段以及类似的技巧。 现在你已经准备好阅读 Mathlib 中的 monoids、groups、rings 和 modules 的定义了。它们比我们在这里看到的要复杂得多，因为它们是一个巨大的层次结构的一部分，但所有的原则都已在上面解释过。

作为一个练习，你可以回到你在上面构建的序关系层次结构，并尝试加入一个类型类`LT₁`，带有小于符号`<₁`，确保每个预排序都带有一个`<₁`，该符号从`≤₁`构建并具有默认值和一个`Prop`-valued字段声明这两个比较运算符之间的自然关系。-/

## 7.2.  Morphisms

在本章中，我们迄今讨论的是如何创建数学结构的层次结构。但是，定义结构的过程不完整，直到我们有了同态。有两种主要的方法。最明显的一种是在函数上定义谓词。

```
def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
  f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'
```

在此定义中，使用并词有些不怡人。尤其是，使用者将需要记住我们选择的顺序，当要访问两个条件时。因此，我们可以使用结构来代替。

```
structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
  map_one : f 1 = 1
  map_mul : ∀ g g', f (g * g') = f g * f g'
```

到了这里，甚至可能需要将其设为一个类，并使用类型类实例解析程序来自动从较简单函数的实例中推断出 `isMonoidHom₂`。例如，monoid态射的复合是monoid态射，这似乎是一个有用的实例。然而，这样的实例对于解析过程来说会很棘手，因为它需要到处追查 `g ∘ f`。看到它在 `g (f x)` 中失败会非常令人沮丧。更通俗的说，一定要记住，在给定表达式中识别哪个函数被应用是个非常棘手的问题，称为“higher-order unification problem”。因此，Mathlib 并没有使用这个类的方法。

一个更基本的问题是：我们是否应使用上述（使用 `def` 或 `structure`）的谓词，或使用将函数和谓词捆绑的structures。这在一定程度上是一个心理问题。考虑一个在monoids之间的函数，而这个函数并不是monoid态射，这是极其罕见的。这真的让人觉得“monoid态射”不是你可以赋予裸函数的形容词，它是一个名词。另一方面，人们可能会反驳，拓扑空间之间的连续函数实际上是一个恰好是连续的函数。这就是为什么 Mathlib 有一个 `Continuous` 谓词的原因。例如，你可以写:

```
example : Continuous (id : ℝ → ℝ) := continuous_id
```

我们仍然有捆绑连续函数，这在例如给连续函数的空间添加拓扑时非常方便，但是它们并不是处理连续性的主要工具。

相反，monoids之间（或其他代数结构）的态射是捆绑在一起的，如下所示：

```
@[ext]
structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
  toFun : G → H
  map_one : toFun 1 = 1
  map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'
```

当然，我们不想到处都键入 `toFun`，所以我们使用 `CoeFun` 类型类注册了一个强制的使用。它的第一个参数是我们想要强制转换为函数的类型。第二个参数描述了目标函数类型。在我们的情况下，对于每一个 `f : MonoidHom₁ G H`，它总是 `G → H`。我们还将 `MonoidHom₁.toFun` 标记为 `coe` 属性，以确保它在策略状态中几乎无形地显示，只需通过 `↑` 前缀即可。

```
instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := MonoidHom₁.toFun

attribute [coe] MonoidHom₁.toFun
```

让我们检查一下，我们确实可以将一个捆起来的monoid态射应用到一个元素上。

```
example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one
```

我们可以对其它类型的态射做同样的事情，直到我们遇到环态射。

```
@[ext]
structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
  toFun : G → H
  map_zero : toFun 0 = 0
  map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
  coe := AddMonoidHom₁.toFun

attribute [coe] AddMonoidHom₁.toFun

@[ext]
structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S
```

这种方法存在一些问题。一个较小的问题是我们不太确定在哪里添加 `coe` 属性，因为 `RingHom₁.toFun` 并不存在，相关的函数是 `MonoidHom₁.toFun ∘ RingHom₁.toMonoidHom₁`，这不是可以被添加属性标记的声明（但我们仍然可以定义一个 `CoeFun  (RingHom₁ R S) (fun _ ↦ R → S)` 实例）。一个更重要的问题是关于monoid态射的引理不能直接应用于环态射。这留下了两个替代方案，要么在每次我们想要应用monoid态射引理时都使用 `RingHom₁.toMonoidHom₁` 来琢磨，要么为环态射重述每一个这样的引理。两者都不吸引人，因此 Mathlib 在这里使用了一个新的层次结构技巧。这个想法是为至少是monoid态射的对象定义一个类型类，并实例化该类为monoid态射和环态射，然后使用它来陈述每一个引理。在下面的定义中，`F` 可以是 `MonoidHom₁ M N`，或者如果 `M` 和 `N` 有一个环的结构，它可以是 `RingHom₁ M N`。

```
class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'
```

然而，上述实施方案存在一个问题。我们还没有注册一个强制到函数实例。让我们尝试现在做。


```
def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₁.toFun
```

使其成为实例将是不利的。当面对如 `f x` 这样的东西时，`f` 的类型不是函数类型，Lean 将尝试找到一个 `CoeFun` 实例来强制将 `f` 转换为函数。上述函数的类型为：`{M N F : Type} → [Monoid M] → [Monoid N] → [MonoidHomClass₁ F M N] → CoeFun F (fun x ↦ M → N)` 所以，在试图应用它时，Lean 不会清楚未知类型 `M`，`N` 和 `F` 应该以哪种顺序推断。这是一种不好的实例，略有不同于我们已经看到的，但归结到的问题一样：不了解 `M` ，Lean 将不得不在未知类型上搜索一个幺半群实例，因此无望尝试数据库中的*每个*幺半群实例。如果你好奇这样的实例的效果，你可以在上述声明顶部键入 `set_option synthInstance.checkSynthOrder false in`，用 `instance` 替换 `def badInst`，并在这个文件中寻找随机的失败。

这里的解决方案很简单，我们需要告诉 Lean 首先搜索什么是 `F`，然后推导 `M` 和 `N`。这是通过 `outParam` 函数完成的。这个函数被定义为恒等函数，但仍被类型类机器识别，并触发了期望的行为。因此，我们可以重新定义我们的类，注意 `outParam` 函数：

```
class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
  toFun : F → M → N
  map_one : ∀ f : F, toFun f 1 = 1
  map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
  coe := MonoidHomClass₂.toFun

attribute [coe] MonoidHomClass₂.toFun
```

现在我们可以继续我们实例化这个类的计划。

```
instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
  toFun := MonoidHom₁.toFun
  map_one := fun f ↦ f.map_one
  map_mul := fun f ↦ f.map_mul

instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
  toFun := fun f ↦ f.toMonoidHom₁.toFun
  map_one := fun f ↦ f.toMonoidHom₁.map_one
  map_mul := fun f ↦ f.toMonoidHom₁.map_mul
```

如承诺的，假设 `f : F` 具有 `MonoidHomClass₁ F`实例，我们证明的每个引理都同时适用于群乘射和环乘射。让我们看一个例子引理并检查它是否适用于两种情况。

```
lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
    f m * f m' = 1 := by
  rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
map_inv_of_inv f h

example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
map_inv_of_inv f h
```

乍一看，我们似乎回到了我们旧的坏主意，使 `MonoidHom₁` 成为一个类。但是我们并没有。所有事情都向上转移到了一个抽象层次。类型类解析过程不会寻找函数，它将寻找 `MonoidHom₁` 或 `RingHom₁`。

我们的方法还有一个问题是存在关于 `toFun` 字段和相应的 `CoeFun` 实例和 `coe` 属性的重复代码。将这个模式仅用于具有额外属性的函数将更好，这意味着应将强制转换到函数视为可注入的。所以 Mathlib 增加了一个更高层次的抽象层，基类 `FunLike`。让我们重新定义我们的 `MonoidHomClass` 在这个基层上。

```
class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
    FunLike F M (fun _ ↦ N) where
  map_one : ∀ f : F, f 1 = 1
  map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
  coe := MonoidHom₁.toFun
  coe_injective' := MonoidHom₁.ext
  map_one := MonoidHom₁.map_one
  map_mul := MonoidHom₁.map_mul
```

当然，映射的层次结构并未在此结束。我们可以继续去定义一个扩展 `MonoidHomClass₃` 的类 `RingHomClass₃` 并在 `RingHom` 上实例化它，然后在 `AlgebraHom` 上再做一次 （代数是带有一些额外结构的环）。但我们已经介绍了 Mathlib 用于映射的主要形式化思想，您应该已经准备好理解 Mathlib 如何定义映射。

作为一项练习，你应该尝试定义有序类型之间的捆绑顺序保持函数类，并然后是顺序保持幺半群同态。这仅为了训练目的。如连续函数一样，顺序保持函数在Mathlib中主要是未捆绑的，它们由 `Monotone` 谓词定义。当然，你需要完成以下的类定义。

```
@[ext]
structure OrderPresHom (α β : Type) [LE α] [LE β] where
  toFun : α → β
  le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

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

在定义了一些代数结构及其变换之后，下一步是考虑继承这种代数结构的集合，例如子群或子环。这在很大程度上与我们之前的主题重叠。事实上，在`X`中的一个集合被实现为一个从`X`到`Prop`的函数，所以子对象是满足某个谓词的函数。因此，我们可以重复利用许多导致`FunLike`类及其后代的想法。我们不会重复使用`FunLike`本身，因为这将破坏从`Set X`到`X → Prop`的抽象屏障。相反，有一个`SetLike`类。该类不是将注入包装为函数类型，而是将其包装为`Set`类型，并定义相应的强制转换和`Membership`实例。

```
@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' := Submonoid₁.ext
```

配备了上述的`SetLike`实例，我们已经可以自然地陈述一个子群`N`包含`1`，而无需使用`N.carrier`。我们也可以安静地将`N`视为`M`中的一个集合，并在映射下取其直接图像。

```
example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N
```

我们也有一个到`Type`的强制转换，它使用`Subtype`，所以给定一个子群`N`，我们可以写一个参数`(x : N)`，它可以被强制转换为属于`N`的`M`的元素。

```
example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property
```

使用这个到`Type`的强制转换，我们也可以解决给子群装备一个群结构的任务。我们将使用上述关于`N`的类型相关的强制转换，以及`SetCoe.ext`引理，该引理断言这种强制转换是可逆的。这两者均由`SetLike`实例提供。

```
instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))
```

注意，在上述实例中，我们可以使用解构绑定器替代使用到`M`的强制转换和调用`property`字段。

```
example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)
```

为了将关于子群的引理应用于子群或子环，我们需要一个类，就像变换一样。请注意，此类接受一个`SetLike`实例作为参数，所以它不需要一个携带者字段，并可以在其字段中使用成员标记。

```
class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem
```

作为练习，你应该定义一个 `子群₁` 结构，为其赋予一个 `集合样` 实例和一个 `子单群类₁` 实例，将一个 `群` 实例放在与 `子群₁` 关联的子类型上，并定义一个 `子群类₁` 类。

关于子对象，一个重要的事实是，在 Mathlib 中，给定代数对象的子对象总是形成一个完全格，并且这个结构被大量使用。例如，你可能找到一个引理，说一个单群的交集是一个单群。但这不是一个引理，而是一个极大值构造。让我们来看看两个单群的情况。

```
instance [Monoid M] : Inf (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩
```

这允许我们得到两个子单群的交集作为一个子单群。

```
example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P
```

你可能认为在上例中我们必须使用最小值符号 `⊓` 而不是交集符号 `∩` 是可惜的。但是，考虑一下极大值。两个子单群的并集并不是一个子单群。然而，子单群仍然形成一个格（甚至是一个完全的）。实际上，`N ⊔ P` 是由 `N` 和 `P` 的并集生成的子单群，当然，用 `N ∪ P` 来表示它会非常混乱。所以你可以看到 `N ⊓ P` 的使用更加一致。它在各种类型的代数结构中更加一致。一开始看到两个向量子空间 `E` 和 `F` 的和表示为 `E ⊔ F` 而不是 `E + F` 可能会有点怪，但你会习惯的。很快你会认为 `E + F` 表示法是一个分心的事，强调的是 `E ⊔ F` 的元素可以写成 `E` 和 `F` 的元素的和，而不是强调 `E ⊔ F` 是包含 `E` 和 `F` 的最小向量子空间这个基本事实。

这一章的最后一个话题是商数操作。我们再次要解释在 Mathlib 中如何构建方便的表示法，并避免代码重复。这里主要的设备是 `HasQuotient` 类，它允许像 `M ⧸ N` 这样的记号。注意，商数符号 `⧸` 是一个特殊的 Unicode 字符，不是一个常规的 ASCII 除号符号。

作为一个例子，我们将构建一个交换单群和一个子单群的商数，把证明留给你。在最后一个例子中，你可以使用 `Setoid.refl`，但它不会自动捕捉到相关的 `Setoid` 结构。你可以通过使用 `@` 语法提供所有参数来解决这个问题，就像 `@Setoid.refl M N.Setoid`。

```
def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
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
  mul_assoc := by
      sorry
  one := QuotientMonoid.mk N 1
  one_mul := by
      sorry
  mul_one := by
      sorry
```
