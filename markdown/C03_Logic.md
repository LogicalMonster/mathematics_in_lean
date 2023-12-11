# 3.  Logic

在上一章中，我们处理了等式，不等式和基本的数学声明，如“$x$除以$y$”。复杂的数学陈述是由这些简单的陈述以及使用逻辑术语如“和”，“或”，“非”，和 “如果...那么”，“每个”，和“一些”，构成的。在本章中，我们将展示如何处理以这种方式构建的声明。

## 3.1.  Implication and the Universal Quantifier

考虑在`#check`之后的声明：

```
#check ∀ x : ℝ, 0 ≤ x → |x| = x
```

用文字来说，我们会说“对于每一个实数`x`，如果`0 ≤ x`，那么`x`的绝对值等于`x`。我们也可以有更复杂的陈述，像：

```
#check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε
```

用文字来说，我们会说“对于每一个 `x` ，`y` 和 `ε` ，如果 `0 < ε ≤ 1`， `x` 的绝对值小于 `ε` ，并且 `y` 的绝对值小于 `ε` ，那么 `x * y` 的绝对值小于 `ε`”。在 Lean 中，在一系列的蕴含关系中有隐含的括号组合在右边。所以上面的表达式意味着“如果`0 < ε`，然后如果`ε ≤ 1`，然后如果`|x| < ε` …"。因此，该表达式表示所有假设一起推导出结论。

你已经看到，尽管本声明中的全称量词涉及到对象，并且蕴含箭头引入假设，Lean以非常相似的方式对待这两方面。特别是，如果你已经证明了那种形式的定理，你可以将它应用到对象和假设上。我们将使用以下陈述作为例子，稍后我们将帮助你证明：

```
theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma a b δ
#check my_lemma a b δ h₀ h₁
#check my_lemma a b δ h₀ h₁ ha hb

end
```

你也已经了解到，在 Lean 中，使用花括号让量化变量变得隐含常常是很普遍的，当我们可以从接下来的假设推断出它们的时候。当我们这样做的时候，我们可以仅仅将引理应用到假设上，而不提及对象。

```
theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
  sorry

section
variable (a b δ : ℝ)
variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
variable (ha : |a| < δ) (hb : |b| < δ)

#check my_lemma2 h₀ h₁ ha hb

end
```

在这个阶段，你也知道，如果你使用 `apply` 策略将 `my_lemma` 应用到形式为 `|a * b| < δ` 的目标，你会得到新的目标，这些目标需要你证明每一个假设。

要证明像这样的声明，使用 `intro` 策略。看看在这个例子中它是如何做的：

```
theorem my_lemma3 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  sorry
```

我们可以为全称量词变量使用任何名字；它们不必是 `x` ， `y` 和 `ε` 。注意我们必须引入变量，尽管它们被标记为隐含：将它们标记为隐含意味着我们在写*使用* `my_lemma` 的表达式时将它们省略，但它们仍然是我们要证明的声明的重要部分。在 `intro` 命令后，目标就是开始时的目标，如果我们在冒号*前*列出所有的变量和假设，就像我们在最后一节所做的那样。稍后，我们将看到为什么有时在证明开始后需要引入变量和假设。

为了帮助你证明引理，我们将给你一些提示：

```
theorem my_lemma4 :
    ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
  intro x y ε epos ele1 xlt ylt
  calc
    |x * y| = |x| * |y| := sorry
    _ ≤ |x| * ε := sorry
    _ < 1 * ε := sorry
    _ = ε := sorry
```

使用定理 `abs_mul` ， `mul_le_mul` ， `abs_nonneg` ， `mul_lt_mul_right` ，和`one_mul` 完成证明。记得你可以使用 Ctrl-space 自动补全（或在 Mac 上使用 Cmd-space 自动补全）找到这些定理。还要记住，你可以使用 `.mp` 和 `.mpr` 或 `.1` 和 `.2` 来提取 if-and-only-if 声明的两个方向。

全称量词经常隐藏在定义中，当必要的时候，Lean 会展开定义来揭示它们。例如，让我们定义两个谓词， `FnUb f a` 和 `FnLb f a` ，其中 `f` 是一个从实数到实数的函数， `a` 是一个实数。第一个说 `a` 是函数 `f` 值的上界，第二个说 `a` 是函数 `f` 值的下界。

```
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x
```

在下一个例子中，`fun x ↦ f x + g x` 是映射 `x` 到 `f x + g x` 的函数。从表达式 `f x + g x` 到此函数的过程在类型理论中称为 lambda 抽象。

```
example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
  intro x
  dsimp
  apply add_le_add
  apply hfa
  apply hgb
```

应用`intro`到目标`FnUb (fun x ↦ f x + g x) (a + b)`强制让Lean展开`FnUb`的定义并为全局量词引入`x`。然后目标变成`(fun (x : ℝ) ↦ f x + g x) x ≤ a + b`。但是应用`(fun x ↦ f x + g x)`到`x`应该产生`f x + g x`，并且`dsimp`命令执行这个简化。（“d”代表“定义性的”。）你可以删除这个命令并且证明仍然有效；Lean必须要执行这个收缩以理解下一个`apply`。`dsimp`命令简单地使目标更容易读，帮助我们弄清楚下一步要做什么。另一个选择是用`change`策略通过写`change f x + g x ≤ a + b`。这帮助让证明更容易阅读，并给你更多控制目标如何被转换的权力。

证明的剩下部分是常规的。最后两个`apply`命令强制Lean展开假设中的`FnUb`的定义。试试进行这些的类似证明：

```
example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
  sorry

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
  sorry

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) :=
  sorry
```

即使我们已经为从实数到实数的函数定义了`FnUb`和`FnUb`，你应该知道这些定义和证明更加通用。这些定义对于任何两种类型之间的函数都是有意义的，只要在它们的值域上有一种序的概念。检查那个定理`add_le_add`的类型显示它适用于任何结构只要这是“有序加法交换幺半群”；现在不要关心这代表什么，但值得知道的是，自然数、整数、有理数和实数都是实例。所以如果我们在这个通用性水平上证明定理`fnUb_add`，那么这个定理将应用于所有这些实例。

```
variable {α : Type*} {R : Type*} [OrderedCancelAddCommMonoid R]

#check add_le_add

def FnUb' (f : α → R) (a : R) : Prop :=
  ∀ x, f x ≤ a

theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
    FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)
```

你已经在[第2.2节](C02_Basics.md#22-Proving-Identities-in-Algebraic-Structures)中看到这样的方括号，尽管我们还没有解释它们的含义。为清楚起见，我们将以实数为主针对大部分的例子，但是值得知道Mathlib包含定义和定理，同时在高级的通用性上都能工作。

作为隐藏全局量词的另一个例子，Mathlib定义了一个谓词`Monotone`，标示一个函数在其参数中是非减的：

```
example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
  @h
```

属性`Monotone f`被定义为与冒号后面的表达是完全一样的。我们需要在`h`前面加上`@`符号，因为如果我们不这样做，Lean将扩展`h`的隐含参数并插入占位符。

证明关于单调性的语句涉及到使用`intro`来引入两个变量，例如，`a`和`b`，以及假设`a ≤ b`。要*使用*单调性假设，你可以将其应用于合适的参数和假设，然后将生成的表达式应用于目标。或者你可以将其应用于目标并让Lean帮助你通过显示剩余的假设作为新的子目标来向后工作。

```
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
  intro a b aleb
  apply add_le_add
  apply mf aleb
  apply mg aleb
```

当证明这么短的时候，提供一个证明项通常会更方便。为描述一个临时引入对象`a`和`b`以及假设`aleb`的证明，Lean使用符号`fun a b aleb ↦ ...`。这与表达式`fun x ↦ x^2`这样以临时命名一个对象，`x`，然后用它来描述一个值的方式有类似性。所以在前面的证明中的`intro`命令对应于下一个证明项中的lambda抽象。然后`apply`命令对应于构建定理应用到它的参数。

```
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
  fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)
```

这里有一个有用的技巧：如果你开始写证明项`fun a b aleb ↦ _`，使用一个下划线作为剩下的表达式应该去的地方，Lean会标记一个错误，表示它不能猜测那个表达式的值。如果你在VS Code中检查Lean Goal窗口或者悬浮在波浪形错误标记上，Lean会显示剩余的表达式需要解决的目标。

试着证明这些，使用策略或者证明项：

```
example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
  sorry

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
  sorry
```

以下是一些更多的例子。如果一个从$\Bbb R$到$\Bbb R$的函数$f$满足$f(-x) = f(x)$对于每一个$x$都成立，那么我们说它是*偶数*；如果$f(-x) = -f(x)$对于每一个$x$都成立，那么我们说它是*奇数*。下面的例子正式定义了这两个概念，并建立了一个关于它们的事实。你可以完成其他的证明。

```
def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
  intro x
  calc
    (fun x ↦ f x + g x) x = f x + g x := rfl
    _ = f (-x) + g (-x) := by rw [ef, eg]


example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
  sorry

example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
  sorry
```

第一个证明可以用`dsimp`或`change`来缩短，以去除lambda抽象。但你可以检查后续的`rw`工作，除非我们明确地去掉lambda抽象，否则它无法在表达式中找到`f x`和`g x`的模式。与某些其他策略不同，`rw`在语法层面上操作，它不会为你展开定义或应用缩小（它有一个变体叫做`erw`，这在这个方向上尝试的稍微更努力一些，但不会更努力多少）。

只要你知道如何发现它们，你可以在任何地方找到隐式的全称量词。

Mathlib包含了一个很好的用于操作集合的库。请记住，Lean不使用基于集合理论的基础，因此这里的集合一词拥有其平凡的含义，即某种给定类型的数学对象的集合`α`。如果`x`的类型为`α`，`s`的类型为`Set α`，那么`x ∈ s`就是一个命题，它断言`x`是`s`的一个元素。如果`y`有一种不同的类型`β`，那么表达式`y ∈ s`就没有意义。在这里，“没有意义”意味着“没有类型，因此Lean不接受它作为一个格式良好的语句”。这与Zermelo-Fraenkel集合理论形成鲜明对比，其中`a ∈ b`对于任何数学对象`a`和`b`都是一个格式良好的语句。例如，`sin ∈ cos`在ZF中是一个格式良好的语句。这个集合理论基础的缺陷是我们在证明助手中不使用它的重要动因，证明助手能帮助我们检测无意义的表达式。在Lean中，`sin`的类型为`ℝ → ℝ`，`cos`的类型为`ℝ → ℝ`，这与`Set (ℝ → ℝ)`不相等，即使在展开定义之后，所以`sin ∈ cos`没有意义。人们也可以使用Lean来处理集合理论本身。例如，连续假设的独立性从Zermelo-Fraenkel的公理已经在Lean中形式化。但是这种集合理论的元理论完全超出了本书的范围。

如果`s`和`t`的类型是`Set α`，那么子集关系`s ⊆ t`被定义为`∀ {x : α}, x ∈ s → x ∈ t`。量词中的变量被标记为隐式的，使得给定`h : s ⊆ t`和`h' : x ∈ s`，我们可以写`h h'`作为`x ∈ t`的理由。下面的例子提供了一个战术证明和一个证明项，证明了子集关系的自反性，并要求你对传递性做同样的事。

```
variable {α : Type*} (r s t : Set α)

example : s ⊆ s := by
  intro x xs
  exact xs

theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
  sorry
```

正如我们为函数定义了`FnUb`，我们可以定义`SetUb s a`表示`a`是集合`s`的一个上界，假设`s`是一种与之相关的具有序的某种类型的元素的集合。在下一个例子中，我们要你证明，如果`a`是`s`的一个界，并且`a ≤ b`，那么`b`也是`s`的一个界。

```
variable {α : Type*} [PartialOrder α]
variable (s : Set α) (a b : α)

def SetUb (s : Set α) (a : α) :=
  ∀ x, x ∈ s → x ≤ a

example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
  sorry
```

我们以一个最后的重要例子结束这一部分。如果对于每个$x_1$和$x_2$，如果$f(x_1) = f(x_2)$就有$x_1 = x_2$，那么我们就说函数$f$是*单射*。Mathlib用`x₁`和`x₂`隐式定义了`Function.Injective f`。下一个例子显示，在实数上，添加常数的任何函数都是单射的。然后，我们要求你证明，如果乘以一个非零常数，那么也是单射的，可以用例子中的引理名作为灵感来源。请记住，在猜测引理名的开头之后，你应该使用Ctrl-space补全。

```
open Function

example (c : ℝ) : Injective fun x ↦ x + c := by
  intro x₁ x₂ h'
  exact (add_left_inj c).mp h'

example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
  sorry
```

最后，证明两个单射函数的组合是单射的：

```
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
  sorry
```

## 3.2.  The Existential Quantifier

存在量词，可以在 VS Code 中输入 `\ex` 来表示，它用于表示“存在”这一概念。在 Lean 中，形式表达式 `∃ x : ℝ, 2 < x ∧ x < 3` 表示存在一个介于 2 和 3 之间的实数。（我们将在[第3.4节](C03_Logic.md#34-Conjunction-and-Iff)中讨论连词符号 `∧`。）证明这样的命题的典型方法是指出一个实数并展示它具有所述的性质。数字 2.5，我们可以将其输入为 `5 / 2` 或 `(5 : ℝ) / 2` ，具有所需的性质，而 `norm_num` 策略可以证明它符合描述。

我们可以通过几种方式将信息放在一起。给定一个以存在量词开始的目标，`use` 策略用于提供对象，留下证明属性的目标。

```
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  use 5 / 2
  norm_num
```

您可以给 `use` 策略提供证据以及数据：

```
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h1 : 2 < (5 : ℝ) / 2 := by norm_num
  have h2 : (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2, h1, h2
```

实际上，`use` 策略会自动尝试使用可用的假设。

```
example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  use 5 / 2
```

或者，我们可以使用 Lean 的*匿名构造符*表示法来构造存在量词的证明。

```
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
  ⟨5 / 2, h⟩
```

注意这里没有 `by`；在这里我们给出了一个显式的证明项。左右角括号可以分别输入为 `\<` 和 `\>` ，它们告诉 Lean 使用适当的构造来整合给出的数据以适应当前的目标。我们可以在不先进入策略模式的情况下使用这个表示法：

```
example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
  ⟨5 / 2, by norm_num⟩
```

所以现在我们知道如何*证明*一个存在的声明。但是我们如何*使用*一个呢？如果我们知道存在具有某种性质的对象，我们应该能够给出一个任意的名字并推理它。例如，记住上一节中的谓词 `FnUb f a` 和 `FnLb f a`，它们表示 `a` 是 `f` 的上界或下界。我们可以使用存在量词来说“`f` 是有界的”而不用指定界限：

```
def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a
```

我们可以使用上一节的定理 `FnUb_add` 来证明，如果 `f` 和 `g` 有上界，那么 `fun x ↦ f x + g x` 也有上界。

```
variable {f g : ℝ → ℝ}

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  rcases ubf with ⟨a, ubfa⟩
  rcases ubg with ⟨b, ubgb⟩
  use a + b
  apply fnUb_add ubfa ubgb
```

`rcases` 策略用于解析存在量词中的信息。像 `⟨a, ubfa⟩` 这样的注释，用与匿名构造符相同的角括号写出，被称为*模式*，它们描述了我们在解析主要参数时期望找到的信息。给定 `f` 存在上界的假设 `ubf`，`rcases ubf with ⟨a, ubfa⟩` 向上下文添加了一个新的变量 `a` 作为上界，同时带有假设 `ubfa` ，表明它具有给定的属性。目标保持不变；改变的是*我们现在可以使用新对象和新假设来证明目标。这是数学推理的一种常见方法：我们解析出一些假设所证明或暗示存在的对象，然后使用它来证明其他东西的存在。

尝试使用此方法来建立以下内容。你可能会发现，将上一节中的一些例子转化为命名定理（如我们所做的 `fn_ub_add`）或者可以直接将论点插入到证明中，将会很有帮助。

```
example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  sorry

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  sorry
```

`rcases` 中的 “r” 代表 “递归”，因为它允许我们使用任意复杂的模式来解析嵌套数据。`rintro` 策略是 `intro` 和 `rcases` 的组合：

```
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
  rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
```

实际上，Lean 也支持在表达式和证明项中的模式匹配函数：

```
example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
  fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩
```

在假设中解包信息的任务如此重要，以至于Lean和Mathlib提供了多种方式来实现它。例如，`obtain`策略提供了建议语法：

```
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  obtain ⟨a, ubfa⟩ := ubf
  obtain ⟨b, ubgb⟩ := ubg
  exact ⟨a + b, fnUb_add ubfa ubgb⟩
```

将第一个 `obtain` 指令视为匹配 `ubf` 的“内容”并用给定的模式，并将组件分配给命名变量。`rcases` 和 `obtain` 被称为 `destruct` 它们的参数，尽管存在一个小的区别，即 `rcases` 在执行完毕后从上下文中清除 `ubf`，而在 `obtain` 之后它仍然存在。

Lean还支持与其他函数式编程语言类似的语法：

```
example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  case intro a ubfa =>
    cases ubg
    case intro b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  cases ubf
  next a ubfa =>
    cases ubg
    next b ubgb =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
  match ubf, ubg with
    | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
      ⟨a + b, fnUb_add ubfa ubgb⟩
```

在第一个示例中，如果你将光标放在 `cases ubf` 后面，你会看到策略生成了一个单一的目标，Lean已将其标记为 `intro`。（特别选用的名称来源于生成存在性声明证明的公理原语的内部名称）然后 `case` 策略命名了组件。第二个例子类似，只不过使用 `next` 代替 `case` 意味着你可以避免提到 `intro`。最后两个例子中的 `match` 单词突出我们在这里做的就是计算机科学家所说的“模式匹配”。注意，第三个证明以 `by` 开始，之后 `match` 的策略版本期望箭头右侧的策略证据。最后一个例子是一个证明项：没有策略可见。

在本书的余下部分，我们将坚持使用 `rcases`，`rintros` 和 `obtain` 作为使用存在性量词的首选方式。但是看看替代语法也无妨，特别是当你有可能找到自己和计算机科学家在一起的时候。

为了说明 `rcases` 如何被使用，我们证明了一个古老的数学问题：如果两个整数 `x` 和 `y` 都可以被写成两个平方的和，那么它们的乘积 `x * y` 也可以。事实上，对于任何可交换的环，这个陈述都是正确的。在下一个例子中，`rcases` 一次解包两个存在性量词。然后我们将需要用来表示 `x * y` 为平方的和的魔法值作为列表提供给 `use` 语句，然后我们使用 `ring` 来验证它们是否有效。

```
variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, xeq⟩
  rcases sosy with ⟨c, d, yeq⟩
  rw [xeq, yeq]
  use a * c - b * d, a * d + b * c
  ring
```

这个证明没有提供多少洞察力，但有一种方法可以激励它。*高斯整数*是形如 $a + bi$ 的数字，其中 $a$ 和 $b$ 是整数，$i = \sqrt{-1}$。高斯整数 $a + bi$ 的*范数*定义为 $a^2 + b^2$。所以高斯整数的范数是平方的和，任何平方的和都可以这样表示。上面的定理反映了高斯整数的乘积的范数是它们的范数的乘积的事实：如果 $x$ 是 $a + bi$ 的范数，并且 $y$ 是 $c + di$ 的范数，那么 $xy$ 是 $(a + bi) (c + di)$ 的范数。我们的奥秘性证明揭示了最容易形式化的证明并不总是最清晰的一个。在[第6.3节](C06_Structures.md#63-Building-the-Gaussian-Integers)，我们将为您提供定义高斯整数并使用它们提供另一种证明的手段。

在存在量词中解包一个方程，然后使用它来重写目标中的表达式的模式经常出现，甚至 `rcases` 策略提供了一个缩写：如果你在新的标识符位置使用关键字 `rfl`，`rcases` 将自动执行重写（这个技巧不能用于模式匹配的 lambda）。

```
theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  rcases sosx with ⟨a, b, rfl⟩
  rcases sosy with ⟨c, d, rfl⟩
  use a * c - b * d, a * d + b * c
  ring
```

就像通用量词一样，如果你知道如何发现它们，你可以在各处找到存在量词。例如，可分性隐含了一个“存在”声明。

```
example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
  rcases divab with ⟨d, beq⟩
  rcases divbc with ⟨e, ceq⟩
  rw [ceq, beq]
  use d * e; ring
```

再次提供一个很好的设置，以便在上述证明中尝试使用 `rcases` 和 `rfl`。感觉很好！

然后尝试证明以下内容：

```
example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  sorry
```

对于另一个重要的例子，如果对于函数 $f : \alpha \to \beta$，对于 codomain 中的每一个 $y$，$\beta$，在 domain，$\alpha$，中存在一个 $x$ 使得 $f(x) = y$，则称函数是 *surjective*。请注意，这个声明包括了万有和存在量，这解释了为什么接下来的例子为什么会使用 ‘intro’ 和 ‘use’。

```
example {c : ℝ} : Surjective fun x ↦ x + c := by
  intro x
  use x - c
  dsimp; ring
```

使用定理 `mul_div_cancel'` 尝试这个示例。

```
example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  sorry
```

在此之后，值得一提的是存在一个策略，`field_simp`，它会以有用的方式清除分母。它可以与 `ring` 策略一起使用。

```
example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
  field_simp [h]
  ring
```

下一个示例通过将其应用于合适的值来使用 surjectivity 假设。请注意，你可以使用 `rcases` 与任何表达式，而不仅仅是假设。

```
example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
  rcases h 2 with ⟨x, hx⟩
  use x
  rw [hx]
  norm_num
```

看看你能否使用这些方法来证明 surjective 函数的构成是 surjective 的。

```
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
  sorry
```

## 3.3.  Negation

符号 `¬` 用来表示否定，因此 `¬ x < y` 表示 `x` 不小于 `y`，`¬ x = y`（或者等价地 `x ≠ y`）表示 `x` 不等于 `y`，以及 `¬ ∃ z, x < z ∧ z < y` 表示没有（不存在）一个 `z` 严格处于 `x` 和 `y` 之间。在 Lean 中，符号 `¬ A` 缩写了 `A → False`，你可以将其理解为 `A` 导致矛盾。从实际意义上讲，这意味着你已经知道了一些如何处理否定的知识：你可以通过引入假设 `h : A` 并证明 `False` 来证明 `¬ A`，如果你有 `h : ¬ A` 和 `h' : A`，那么将 `h` 应用于 `h'` 将产生 `False`。

为了说明，考虑严格排序的不反射性原理 `lt_irrefl`，它说明我们对每一个 `a` 都有 `¬ a < a`。对称性原理 `lt_asymm` 说明我们有 `a < b → ¬ b < a`。让我们证明 `lt_asymm` 是由 `lt_irrefl` 而来的。

```
example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this
```

这个示例介绍了一些新的技巧。首先，当你在没提供标签的情况下使用 `have` 的时候，Lean 会使用名字 `this`，提供了一个便捷的方式来引用它。因为证明非常简短，我们提供了一个显式的证明项。但是你真正应该关注的是在这个证明中 `intro` 调用的结果，它使一个假想的 `False`，和我们最终通过将 `lt_irrefl` 应用于一个 `a < a` 的证明来证明 `False`。

这是另一个示例，它使用了在最后一节中定义的谓语 `FnHasUb`，该谓语的意思是一个函数有一个上界。

```
example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨a, fnuba⟩
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith
```

请记住，当一个目标来源于上下文中的线性等式和不等式时，使用 `linarith` 通常很方便。

看看你能否用类似的方式证明这些：

```
example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
  sorry

example : ¬FnHasUb fun x ↦ x :=
  sorry
```

Mathlib 提供了许多用于关联排列和否定的有用定理：

```
#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)
```

回顾谓词 `Monotone f`，该谓词表明 `f` 是非递减的。使用一些刚刚列举的定理来证明以下的命题：

```
example (h : Monotone f) (h' : f a < f b) : a < b := by
  sorry

example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  sorry
```

我们可以看到如果我们用 `≤` 替换 `<`，那么最后的例子中的第一个例子将无法证明。注意，我们可以通过给出反例来证明泛化语句的否定。完成证明.

```
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by sorry
  have h' : f 1 ≤ f 0 := le_refl _
  sorry
```

这个例子引入了 `let` 的策略，这增加了一个*局部定义*到上下文中。如果你把光标放在 `let` 命令后面，在目标窗口中你会看到定义 `f：ℝ→ℝ：= fun x ↦ 0` 已经添加到上下文中。Lean 在必要时会展开 `f` 的定义。特别的，当我们用`le_refl`证明 `f 1 ≤ f 0`时，Lean将 `f 1` 和 `f 0`简化为 `0`。

使用 `le_of_not_gt` 来证明如下：

```
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
  sorry
```

在我们刚做的许多证明中，一个隐含的事实是,如果 `P` 是任何属性，没有属性 `P` 的东西相同于所有东西都不具有属性 `P`，而不是所有东西都有属性 `P` 相当于有些东西不具有属性 `P`。换句话说，以下四个含义都是有效的 (但其中一个我们还不能用我们目前解释的内容证明)：

```
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  sorry

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  sorry

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  sorry

example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry
```

第一，第二和第四个可以直接用你已经看到的方法证明。我们建议你试试。然而，第三个更困难，因为它从一个对象的不存在是矛盾的事实中得出该对象的存在。这是*经典*数学推理的一个实例。我们可以使用反证法来证明第三个含义，如下所示。

```
example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩
```

确保你理解这是如何工作的。`by_contra` 策略允许我们通过假设 `¬ Q` 并引出矛盾来证明目标 `Q`。事实上，它等同于使用等价 `not_not : ¬ ¬ Q ↔ Q`。确认你可以使用 `by_contra` 来证明这个等价的正向方向，而反向方向可以根据一般的否定规则得出。

```
example (h : ¬¬Q) : Q := by
  sorry

example (h : Q) : ¬¬Q := by
  sorry
```

使用反证法来建立以下，这是我们以上证明的含义的一个逆命题。 (提示：先使用 `intro`。)

```
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  sorry
```

使用包含否定的复合语句通常很繁琐，常见的数学模式是将这样的语句替换为等价形式，其中否定被推入内部。为了便于这样做，Mathlib 提供了一个 `push_neg` 策略，这种策略以这种方式重新声明目标。命令 `push_neg at h` 重新声明假设 `h`。

```
example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h
```

在第二个例子中，我们使用 dsimp 来展开 `FnHasUb` 和 `FnUb` 的定义。 (我们需要使用 `dsimp` 而不是 `rw` 来展开 `FnUb`，因为它出现在量词的范围内。)你可以验证 `¬∃ x, P x` 和 `¬∀ x, P x` 的上述示例中，`push_neg` 策略做了预期的事情。即使你不知道如何使用 conjunction 符号，你也应该能够使用 `push_neg` 证明以下：

```
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  sorry
```

Mathlib 还有一个策略，`contrapose`，它将目标 `A → B` 转化为 `¬B → ¬A`。同样，给定从假设 `h：A` 推出 `B` 的目标，`contrapose h` 让你有一个从假设 `¬B` 推出 `¬A` 的目标。使用 `contrapose!` 而不是 `contrapose` 将 `push_neg` 应用于目标和相关假设。

```
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith
```

我们还没有解释`构造器`命令或者在其后使用的分号，但我们将在下一节中进行说明。

我们以*ex falso*的原则结束这一节，该原则表明任何事情都源于矛盾。在Lean中，这通过`False.elim`表示，它建立了`False → P`的任何命题`P`。这可能看起来像一个奇怪的原则，但它却经常出现。我们经常通过在案例上进行拆分来证明一个定理，有时我们可以证明其中一个案例是矛盾的。在这种情况下，我们需要断定矛盾确立了目标，这样我们才能继续进行下一个案例（我们将在[Section 3.5]（C03_Logic.md#35-Disjunction）中看到案例推理的实例）。

一旦达到矛盾，Lean提供了多种结束目标的方法。

```
example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction
```

`exfalso`策略用证明`False`的目标替换当前的目标。给定`h : P`和`h' : ¬ P`，项`absurd h h'`可以确定任何命题。最后，`contradiction`策略试图通过在假设中找到矛盾来结束一个目标，例如形式`h : P`和`h' : ¬ P`的一对。当然，在这个例子中，`linarith`也同样有效。

## 3.4.  Conjunction and Iff

你已经看到了连接符号，`∧`，用于表示“以及”。`构造器`策略允许你证明`A ∧ B`形式的声明，方法是首先证明`A`然后证明`B`。

```
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
  constructor
  · assumption
  intro h
  apply h₁
  rw [h]
```

在此示例中，`假设`策略告诉Lean找一个可以解决目标的假设。注意最后的`rw`通过应用` ≤ `的反射来完成目标。以下是使用匿名构造函数的角括号来执行前面例子的替代方法。第一个是一个将在关键字`by`处进入策略模式的精炼的证明项版本。

```
example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
  have h : x ≠ y := by
    contrapose! h₁
    rw [h₁]
  ⟨h₀, h⟩
```

*使用*一个并行而不是证明一个并行涉及到解开两部分的证据。你可以使用`rcases`策略来实现，同样也可以使用`rintro`或模式匹配的`fun`，所有这些都与存在量词的使用方法类似。

```
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  rcases h with ⟨h₀, h₁⟩
  contrapose! h₁
  exact le_antisymm h₀ h₁

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩ h'
  exact h₁ (le_antisymm h₀ h')

example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
  fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')
```

与`obtain`策略类似，还有一个模式匹配的`have`：

```
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  have ⟨h₀, h₁⟩ := h
  contrapose! h₁
  exact le_antisymm h₀ h₁
```

与`rcases`相比，这里的`have`策略在上下文中保留了`h`。尽管我们不会使用它们，但我们再次得到了计算机科学家的模式匹配语法：

```
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  case intro h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  cases h
  next h₀ h₁ =>
    contrapose! h₁
    exact le_antisymm h₀ h₁

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  match h with
    | ⟨h₀, h₁⟩ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁
```

与使用存在量化器相反，你可以通过写`h.left`和`h.right`或等价的`h.1`和`h.2`来提取假设`h : A ∧ B`的两个组件的证据。

```
example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
  intro h'
  apply h.right
  exact le_antisymm h.left h'

example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
  fun h' ↦ h.right (le_antisymm h.left h')
```

尝试使用这些技巧来提出以下各种证明方法：

```
example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
  sorry
```

您可以使用 `∃` 和 `∧` 的匿名构造器，`rintro` 和 `rcases` 进行嵌套。

```
example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
  ⟨5 / 2, by norm_num, by norm_num⟩

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
  rintro ⟨z, xltz, zlty⟩
  exact lt_trans xltz zlty

example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
  fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty
```

您也可以使用 `use` 策略：

```
example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
  use 5 / 2
  constructor <;> norm_num

example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
  use 5
  use 7
  norm_num

example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
  rintro ⟨h₀, h₁⟩
  use h₀
  exact fun h' ↦ h₁ (le_antisymm h₀ h')
```

在第一个例子中，`构造器` 命令后的分号告诉 Lean 对结果的两个目标使用 `norm_num` 策略。

在 Lean 中，`A ↔ B` *不* 被定义为 `(A → B) ∧ (B → A)`，但它可能是这样，并且大致以相同的方式运作。您已经看到，您可以为 `h: A ↔ B` 的两个方向写 `h.mp` 和 `h.mpr` 或 `h.1` 和 `h.2`。您也可以使用 `cases` 和朋友们。为了证明一个当且仅当的命题，您可以使用 `constructor` 或尖括号，就像您证明连词时那样。

```
example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
  constructor
  · contrapose!
    rintro rfl
    rfl
  contrapose!
  exact le_antisymm h

example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
  ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩
```

最后一个证明条目是深不可测的。记住，当您正在写一个像那样的表达式时，可以使用下划线来查看 Lean 的期望。

尝试使用您刚刚看到的各种技巧和小玩意来证明以下命题：

```
example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
  sorry
```

对于一个更有趣的练习，展示对于任何两个实数 `x` 和 `y`，`x^2 + y^2 = 0` 当且仅当 `x = 0` 和 `y = 0`。我们建议使用 `linarith`，`pow_two_nonneg` 和 `pow_eq_zero` 来证明一个辅助引理。

```
theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
  have h' : x ^ 2 = 0 := by sorry
  pow_eq_zero h'

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 :=
  sorry
```

在 Lean 中，双向蕴含引导一种双重生活。您可以像处理连接词一样来分开处理它的两个部分。但 Lean 也知道，它是命题之间的反射、对称和可传递的关系，您也可以与 `calc` 和 `rw` 一起使用它。经常方便地将一个声明重写为相等的声明。在下一个例子中，我们使用 `abs_lt` 将形式为 `|x| < y` 的表达式替换为等价的表达式 `- y < x ∧ x < y`，在之后的一个例子中我们使用 `Nat.dvd_gcd_iff` 将形式为 `m | Nat.gcd n k` 的表达式替换为等价的表达式 `m | n ∧ m | k`.

```
example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
  rw [abs_lt]
  intro h
  constructor <;> linarith

example : 3 ∣ Nat.gcd 6 15 := by
  rw [Nat.dvd_gcd_iff]
  constructor <;> norm_num
```

看看你是否可以使用下面的定理 `rw` 提供一个简短的证据，证明否定是不是一个非递减的函数。(注意，`push_neg` 不会为你展开定义，所以定理的证明中需要 `rw [Monotone]`。)

```
theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  rw [Monotone]
  push_neg
  rfl

example : ¬Monotone fun x : ℝ ↦ -x := by
  sorry
```

本节剩余的练习旨在让你对合取和双向蕴含有更多的实践。记住，*部分排序*是一个二元关系，它是传递的，自反的，和反对称的。一个更弱的概念有时会出现：一个 *预排序* 仅仅是一个自反的，传递的关系。对任何预排序 `≤`，Lean 将关联的严格预排序通过 `a < b ↔ a ≤ b ∧ ¬ b ≤ a` 进行公理化。展示如果 `≤` 是一个部分排序，那么 `a < b` 等价于 `a ≤ b ∧ a ≠ b`：

```
variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
  rw [lt_iff_le_not_le]
  sorry
```

除了逻辑操作，你不需要 `le_refl` 和 `le_trans` 以外的任何东西。即使在 `≤` 只被假定为预排序的情况下，我们也能证明严格顺序是不可反射的和传递的。在第二个示例中，为了方便，我们使用简化器而不是 `rw` 来表示 `<` 关于 `≤` 和 `¬` 的表达式。我们会在后面再回来讨论简化器，但在这里我们只依赖于它会不断使用指示的引理，即使它需要被实例化为不同的值。

```
variable {α : Type*} [Preorder α]
variable (a b c : α)

example : ¬a < a := by
  rw [lt_iff_le_not_le]
  sorry

example : a < b → b < c → a < c := by
  simp only [lt_iff_le_not_le]
  sorry
```

## 3.5.  Disjunction

证明析取 `A ∨ B` 的规范方法是证明 `A` 或 `B`。`左`策略选择 `A`，`右` 策略选择 `B`。

```
variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]
```
我们不能使用一个匿名构造器来构造一个“或”的证明，因为 Lean 必须猜测我们试图证明哪个析取。当我们写证明项时可以使用 `Or.inl` 和 `Or.inr` 来代替明确地做出选择。此处，`inl` 是“introduction left”的简写，而 `inr` 是“introduction right”的简写。

```
example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h
```

证明一个隐含的或者显示的析取在假设和数据中通常取决于案例区分，可能变得有点奇怪。 `rcases` 策略允许我们使用形式为 `A ∨ B` 的假设。和使用 `rcases` 的联接或存在量词形成鲜明对比的是，这里的 `rcases` 策略会产生两个目标。两者都有相同的结论，但在第一种情况下，假设 `A` 为真，而在第二种情况下，假设 `B` 为真。换句话说，就像名字所暗示的，`rcases` 策略执行情况下的证明。通常情况下，我们可以告诉 Lean 使用的假设名称。在下一个例子中，我们告诉 Lean 在每一个分支上使用名称 `h`。

```
example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h
```

注意模式从联结的`⟨h₀, h₁⟩`变成了析取的 `h₀ | h₁`。将第一个模式看作匹配包含 `h₀` 和 `h₁` 的两个数据，而第二个模式，带有一个条形的模式，匹配包含 `h₀` 或 `h₁` 的数据。在这种情况下，由于两个目标是独立的，我们选择在每个案例中使用相同的名称，`h`。

绝对值函数被定义为 `x ≥ 0` 蕴含 `|x| = x`（这就是定理 `abs_of_nonneg`）并且 `x < 0` 蕴含 `|x| = -x`（这就是 `abs_of_neg`）。表达式 `le_or_gt 0 x` 确立 `0 ≤ x ∨ x < 0`，这样我们就可以在这两种情况中进行分割。

Lean 也支持计算机科学家的析取的模式匹配语法。现在 `cases` 策略更具吸引力，因为它让我们能够命名每一 `case`，并在引入假设用于何处时命名它。

```
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h
```

名字 `inl` 和 `inr` 是 “intro left” 和 “intro right”的简称。 使用 `case` 的优势是你可以按任意顺序证明案例；Lean 使用标记来找到相关的目标。如果你不关心那个，你可以使用 `next`，或者 `match`，甚至可以使用匹配模式的 `have`.

```
example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h
```

在`match`的情况下，我们需要使用原始方法证明一个析取的全名`Or.inl`和`Or.inr`。在这个教科书中，我们通常会使用`rcases`来对析取的情况进行分解。

试着用下面片段的前两个定理来证明三角不等式。它们是在Mathlib中的原名。

```
namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  sorry

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  sorry
```

如果你喜欢这些（打算如此）并且你想有更多的析取练习，试试这些。

```
theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  sorry

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  sorry
```

你也可以使用`rcases`和`rintro`来处理嵌套的析取。当这些导致一个真正的案例分解与多个目标时，每个新目标的模式都由一个垂直条分隔。

```
example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt
```

你仍然可以嵌套模式并使用`rfl`关键字来代替等式：

```
example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right
```

看看你是否可以使用一条（很长的）线进行证明。使用`rcases`来解包假设并分解案例，并使用分号和`linarith`来解决每个分支。

```
example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry
```

对于实数，一个方程`x * y = 0`告诉我们`x = 0`或`y = 0`。在Mathlib中，这个事实被称为`eq_zero_or_eq_zero_of_mul_eq_zero`，它是如何产生一个析取的另一个很好的例子。看看你能否用它来证明以下的内容：

```
example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
```

记住你可以使用`ring`策略来帮助计算。

在一个任意的环$R$中，一个元素$x$使得$x y = 0$对于某个非零$y$被称为*左零因子*，一个元素$x$使得$y x = 0$对于某个非零$y$被称为*右零因子*，而一个要么是左零因子要么是右零因子的元素简单地被称为*零因子*。定理`eq_zero_or_eq_zero_of_mul_eq_zero`说实数没有非平凡的零因子。一个具有此属性的交换环被称为*整环*。你应该在任何整环中证明上述两个定理：

```
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry
```

实际上，如果你仔细的话，可以在不使用乘法交换律的情况下证明第一个定理。在那种情况下，只需假设 `R` 是一个 `Ring` 而非 `CommRing`。

有时在证明中我们想要根据某些叙述是否为真来进行分情况处理。对于任何命题 `P`，我们可以使用 `em P : P ∨ ¬ P`。名称 `em` 是 “excluded middle” 的简写。

```
example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction
```

或者，你可以使用 `by_cases` 策略。

```
example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction
```

注意 `by_cases` 策略使你可以为每个分支中引入的假设指定一个标签，比如在这个案例中，`h' : P` 在一个分支中，`h' : ¬ P` 在另一个，如果你省略了标签，Lean 默认使用 `h`。试着证明下面的等价性，使用 `by_cases` 来建立一个方向。

```
example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
```

## 3.6.  Sequences and Convergence

现在我们已经掌握了足够的技能来做一些真实的数学工作。在 Lean 中，我们可以将实数序列 $s_0, s_1, s_2, \ldots$ 表示为函数 `s : ℕ → ℝ`。如果对于任何 $\varepsilon > 0$，存在一个点在该点之后序列保持在 $a$ 附近的 $\varepsilon$ 范围内，也就是存在一个数 $N$，对于任何 $n \ge N$，$| s_n - a | < \varepsilon$，那么这样的序列就称为向数 $a$ *收敛*。在 Lean 中，我们可以这样描述：

```
def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
```

记号 `∀ ε > 0, ...` 是 `∀ ε, ε > 0 → ...` 的一个便捷缩写，同样，`∀ n ≥ N, ...` 缩写了 `∀ n, n ≥ N →  ...`。另外记住，`ε > 0` 定义为 `0 < ε`，`n ≥ N` 定义为 `N ≤ n`。

在本节中，我们将建立一些收敛的性质。但首先，我们会讨论一下与等式处理有关的三种策略，这将被证明是有用的。第一种，`ext`策略，为我们提供了证明两个函数相等的方法。让 $f(x) = x + 1$ 和 $g(x) = 1 + x$ 是从实数到实数的函数。那么，当然，$f = g$，因为它们返回的值对于每一个 $x$ 都是相同的。`ext` 策略使我们能够通过证明函数在所有参数的值上的值是相同的来证明函数之间的等式。

```
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring
```

稍后我们会看到 `ext` 实际上更一般，也可以指定出现的变量的名称。例如，你可以尝试在上述证明中用 `ext u v` 替换 `ext`。第二种策略，`congr` 策略，允许我们通过调和不同的部分来证明两个表达式之间的等式：

```
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring
```

在这里 `congr` 策略去掉了每一边的 `abs`，留下我们来证明 `a = a - b + b`.

最后，`convert` 策略被用来在定理的结论不完全匹配时将一个定理应用到目标上。例如，假设我们要从 `1 < a` 证明 `a < a * a`。一个在库中的定理，`mul_lt_mul_right`，会让我们证明 `1 * a < a * a`。一种可能性是反向工作并重新写目标，使其具有该形式。相反，`convert` 策略让我们可以原封不动地应用定理，并留下我们证明需要让目标匹配的等式的任务。

```
example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h
```

此例子举例说明了一个有用的技巧：当我们应用一个带下划线的表达式时，如果 Lean 不能自动为我们填充它，它就会将它留给我们作为另一个目标。

以下证明任何常数序列 $a, a, a, \ldots$ 收敛。

```
theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos
```

Lean 有一个策略，`simp`，它可以经常帮助你省去手动执行如 `rw [sub_self, abs_zero]` 这样的步骤。我们会尽快给你提供更多信息。

对于一个更有趣的定理，让我们证明如果 `s` 收敛于 `a`，`t` 收敛于 `b`，那么 `fun n ↦ s n + t n` 收敛于 `a + b`。在开始编写正式的证明之前，有明确的纸和笔的证明是有帮助的。给定大于 `0` 的 `ε`，主要的想法是使用假设获得一个 `Ns`，使得在那个点之后，`s` 在 `a` 的 `ε / 2` 范围内，以及一个 `Nt`，使得在那个点之后，`t` 在 `b` 的 `ε / 2` 范围内。然后，无论 `n` 是否大于或等于 `Ns` 和 `Nt` 的最大值，序列 `fun n ↦ s n + t n` 都应在 `a + b` 的 `ε` 以内。下面的例子开始实现了这个策略。试着看看你能不能完成它。

```
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  sorry
```

作为提示，您可以使用 `le_of_max_le_left` 和 `le_of_max_le_right`，并且 `norm_num` 可以证明 `ε / 2 + ε / 2 = ε`。此外，使用 `congr` 策略显示 `|s n + t n - (a + b)|` 等于 `|(s n - a) + (t n - b)|，`是有帮助的，因为然后您可以使用三角不等式。请注意，我们将所有变量 `s`、`t`、`a` 和 `b` 标记为隐含的，因为它们可以从假设中推断出来。

使用乘法代替加法来证明相同的定理是有难度的。我们将首先证明一些辅助陈述。看看您是否也能完成接下来的证明，该证明显示如果 `s` 收敛于 `a`，那么 `fun n ↦ c * s n` 收敛于 `c * a`。根据 `c` 是否等于零分成不同的情况是有帮助的。我们已经处理了零的情况，留给您证明在 `c` 非零的额外假设下的结果。

```
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  sorry
```

下一个定理也有独立的意思：它显示了一个收敛序列在绝对值上最终是有界的。我们已经开始了你的工作，看看你能不能完成它。

```
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  sorry
```

事实上，定理可以被加强为断言有一个边界 `b` 适用于 `n` 的所有值。但是这个版本已经足够强大，可以满足我们的需要，我们将在这一部分的末尾看到，它更普遍地适用。

下一个引理是辅助的：我们证明，如果 `s` 收敛至 `a`，且 `t` 收敛至 `0`，则 `fun n ↦ s n * t n` 收敛至 `0`。为此，我们使用前面的定理找到一个 `B`，该点超过某个点 `N₀`对 `s`进行界定。看看你能否理解我们提出的策略，并完成证明。

```
theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  sorry
```

如果你已经做到了这一步，恭喜！我们现在已经快要完成我们的定理了。下面的证明完成了它。

```
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring
```

对于另一个具有挑战性的练习，尝试填写以下证明极限是独特的证明概述。 (如果你感觉大胆，你可以删除证明草图并尝试从头开始证明。)

```
theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by sorry
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by sorry
  have absb : |s N - b| < ε := by sorry
  have : |a - b| < |a - b| := by sorry
  exact lt_irrefl _ this
```

我们以观察我们的证明可以被一般化来结束这一部分。例如，我们使用的自然数的唯一属性是其结构具有 `min` 和 `max` 的偏序。您可以检查如果你用任何线性顺序 `α` 替换 `ℕ` ，一切仍然可行：

```
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε
```

在[第9.1节](C09_Topology.md#91-filters)中，我们将看到Mathlib具有处理收敛性的各种机制，不仅可以抽象掉域和值域的特定特征，而且还可以对不同类型的收敛性进行抽象。
