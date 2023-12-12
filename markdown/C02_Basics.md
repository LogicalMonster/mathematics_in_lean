# 2.  Basics

本章旨在向您介绍 Lean 中的数学推理的基本要素: 计算，应用引理和定理，以及推理有关的通用结构。

## 2.1.  Calculating

我们通常学习进行数学计算，而不把它们当作证明。但是，当我们验证计算中的每一步，就像 Lean 要求我们做的那样，结果就是一个证明，证明计算的左手边等于右手边。

在 Lean 中，陈述一个定理等同于陈述一个目标，即，证明定理的目标。Lean 提供了重写策略 `rw`，用于在目标中将等式的左手边替换为右手边。如果 `a`、 `b` 和 `c` 是实数，`mul_assoc a b c` 是等式 `a * b * c = a * (b * c)`，`mul_comm a b` 是等式 `a * b = b * a`。Lean 提供了自动化常规消除调用这些事实的需要，但它们对于说明例子有用。在 Lean 中，乘法关联到左边，所以 `mul_assoc` 的左手边也可以写作 `(a * b) * c`。但是，按照 Lean 的记数法惯例，通常忽略括号是一种很好的风格。

让我们试着使用 `rw`。

```
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc b a c]
```

在关联的示例文件开始的 `import` 行导入了来自 Mathlib 的实数理论，以及有用的自动化工具。为了简洁起见，我们通常在教科书中压制这样的信息。

欢迎您进行更改，看看会发生什么。您可以在 VS Code 中键入 `\R` 或 `\real` 字符以打出 `ℝ`。您击键或者按 Tab 键后，符号才会出现。在阅读 Lean 文件时，如果你把鼠标悬停在一个符号上，VS Code 将显示你可以用来输入它的语法。如果你好奇所有可用的缩写，你可以按 Ctrl-Shift-p，然后输入缩写来访问 `Lean 4: Show all abbreviations` 命令。如果你的键盘没有容易访问的反斜杠，你可以通过改变 `lean4.input.leader` 设置来改变前导字符。

当一个光标在一个策略证明的中间时，Lean 在 `Lean infoview` 窗口中报告当前的*证明状态*。当你把鼠标移动过每一步证明，你可以看到状态的变化。Lean 中的典型证明状态可能如下所示：

```
1 goal
x y : ℕ,
h₁ : Prime x,
h₂ : ¬Even x,
h₃ : y > x
⊢ y ≥ 4
```

以 `⊢` 开始的行之前的行表示*上下文*：它们是当前在发挥作用的对象和假设。在这个例子中，这些包括两个对象，`x` 和 `y`，都是自然数。它们还包括三个假设，标记为 `h₁`，`h₂` 和 `h₃`。在 Lean 中，上下文中的所有内容都用标识符标记。你可以用 `h\1`，`h\2` 和 `h\3` 输入这些加下标的标签，但任何合法的标识符都可以：你可以用 `h1`，`h2`，`h3`，或者 `foo`，`bar`，`baz`。最后一行代表*目标*，也即，需要被证明的事实。有时候，人们使用*目标*表达需要被证明的事实，使用*目标*表示上下文和目标的组合。在实践中，通常清楚地表示了预期的含义。

尝试证明这些等式，每种情况下用策略证明替换 `sorry`。使用 `rw` 策略，你可以用左箭头 (`\l`) 来反转一个等价关系。例如，`rw [← mul_assoc a b c]` 用 `a * b * c` 替换了当前目标中的 `a * (b * c)`。注意，左指向箭头指的是从 `mul_assoc` 提供的等价关系的右边到左边，它与目标的左边或右边无关。

```
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
```

您还可以使用类似 `mul_assoc` 和 `mul_comm` 的等式作为未带参数使用。在这种情况下，重写策略尝试将左手边与目标中的一个表达式匹配，使用它找到的第一个模式。

```
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
```

你也可以提供*部分*信息。例如，`mul_comm a` 匹配任何形如 `a * ?` 的模式，将它重写成 `? * a`。尝试再不提供任何参数的情况下做第一个例子，只用一个参数来做第二个例子。

```
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
```

您还可以使用来自本地上下文的事实与 `rw`一起使用。

```
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
```

尝试这些，使用定理 `sub_self` 来完成第二个：

```
example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  sorry

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  sorry
```

可以使用单个命令执行多个重写命令，方法是在方括号内以逗号分隔列出相关的身份。

```
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
```

您仍然可以通过在任何重写列表中的逗号后放置光标来查看增量进度。

另一个技巧是我们可以一劳永逸地在一个例子或定理外部声明变量。Lean 然后自动包括它们。

```
variable (a b c d e f : ℝ)

example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
```

在上述证据开始时检查策略状态，Lean 确实包括了所有变量。我们可以通过将其放在 `section ... end` 块中来限制声明的范围。最后，回顾一下介绍，Lean 为我们提供了一个命令来确定表达式的类型：

```
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
```

`#check` 命令适用于对象和事实。对命令 `#check a` 的响应，Lean 报告说 `a` 的类型是 `ℝ`。对命令 `#check mul_comm a b` 的回应，Lean 报告说 `mul_comm a b` 是事实 `a * b = b * a` 的证明。命令 `#check (a : ℝ)` 声明了我们对 `a` 的类型是 `ℝ` 的期望，如果不是这样，Lean 会抛出一个错误。我们将在稍后解释最后三个 `#check` 命令的输出，但与此同时，你可以看一看它们，并用一些 `#check` 命令进行实验。

让我们再试些例子，定理 `two_mul a` 表示 `2 * a = a + a`。定理 `add_mul` 和 `mul_add` 表达乘法在加法上的可分配性，定理 `add_assoc` 表达了加法的结合性。使用 `#check` 命令查看精确的声明。

```
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]
  rw [← add_assoc, add_assoc (a * a)]
  rw [mul_comm b a, ← two_mul]
```

而我们可以通过在编辑器中逐步完成这个证明来弄清楚这个证明的内容，很难单独阅读。Lean 使用 `calc` 关键字提供了一种更结构化的写证明的方式。

```
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
```
请注意，证明 *并不是* 以 `由` 开始：一个以 `calc` 开始的表达式是一个 *证明项*。在策略证明中也可以使用 `calc` 表达式，但 Lean 将其解释为使用结果证明项解决目标的指令。`calc` 语法有点挑剔：下划线和证明需要按照上面指示的格式。Lean 使用缩进来确定诸如策略块或 `calc` 块的开始和结束位置；尝试改变上面证据中的缩进，看看会发生什么。

编写 `calc` 证明的一种方法是先用 `sorry` 策略为证明，确保 Lean 接受这些表达式，然后用策略证明每个步骤。

```
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
```

试试用一个纯 `rw` 证明和一个更结构化的 `calc` 证明证明以下身份：

```
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
  sorry
```

以下练习略有挑战性。你可以使用下面列出的定理。
```
example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  sorry

#check pow_two a
#check mul_sub a b c
#check add_mul a b c
#check add_sub a b c
#check sub_sub a b c
#check add_zero a
```

我们也可以在上下文中的假设中进行重写。例如，`rw [mul_comm a b] at hyp` 在假设 `hyp` 中将 `a * b` 替换为 `b * a`。

```
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp
```

在最后一步，`exact` 策略可以使用 `hyp` 来解决目标，因为在那个时候 `hyp` 正好匹配目标。

我们通过注意到 Mathlib 提供了一个有用的 `ring` 策略来结束这一节，该策略旨在证明任何交换环中的恒等式，只要它们仅源于环公理，而不使用任何局部假设。

```
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
```

`ring` 策略在我们导入 `Mathlib.Data.Real.Basic` 时间接导入，但我们将在下一节中看到，除了实数之外，还可以用于其他结构的计算。它可以通过命令 `import Mathlib.Tactic` 显式导入。我们将看到有类似策略的其他常见代数结构。

`rw` 有一个变体 `nth_rewrite`，它允许您仅替换目标中表达式的特定实例。可能的匹配从 1 开始编号，所以在以下示例中，`nth_rewrite 2 h` 将 `a + b` 的第二次出现替换为 `c`。

```
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]
  rw [add_mul]
```

## 2.2. Proving Identities in Algebraic Structures

在数学中，一个环由对象集合、操作 +、×，常数 0, 1，和操作 $x\mapsto -x$ 组成，它们满足：

  - $R$ 与 + 是阿贝尔群，0 是加法单位，负是逆。

  - 乘法是与单位 1 的关联性，并且乘法是加法的分配。

在 Lean 中，对象的集合表示为类型 `R`。环公理如下：

```
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
```

在第一行中，方括号的含义稍后会详细介绍，但在此之前，足以说明该声明给我们提供了一种类型 `R` 和 `R` 上的环结构。然后 Lean 允许我们使用 `R` 元素的通用环符号，并利用有关环的定理库。

一些定理的名称应该看起来很熟悉：它们正是我们在上一节中用来计算实数的。Lean 不仅能证明关于具体数学结构的事情，如自然数和整数，还能证明关于以公理化方式表征的抽象结构，如环。此外，Lean 支持关于抽象和具体结构的泛型推理，并且可以被训练来识别适当的实例。因此，关于环的任何定理都可以应用到整数 `ℤ`、有理数 `ℚ` 和复数`ℂ` 这样的具体环。它还可以应用到任何扩展环的抽象结构实例，如任何有序环或任何域。

然而，并非所有有关实数的重要性质都在任意环中成立。例如，实数的乘法是可交换的，但这在一般情况下并不成立。如果您修过线性代数课程，您会认识到，对于每个 $n$，实数的$n$行$n$列矩阵形成了一个环，在其中通常不满足交换性。实际上，如果我们声明 `R` 是一个交换环，那么当我们用 `R` 替换 `ℝ` 时，上一节中的所有定理都将继续成立。

```
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
```

我们将验证所有其他证明是否通过的任务留给您。请注意，当证明很短，如`by ring`，`by linarith`或`by sorry`时，通常（并允许）将它放在`by`的同一行上。良好的证明写作风格应在简洁性和可读性之间取得平衡。

本节的目标是加强您在上一节中开发的技能，并将它们应用于公理化对环的推理。我们将从上面列出的公理开始，并用它们来推导其他事实。我们证明的大部分事实已经存在于Mathlib中。我们将为我们证明的版本赋予相同的名称，以帮助您学习库的内容以及命名约定。

Lean提供了类似于编程语言中使用的组织机制：当在*命名空间* `bar`中引入定义或定理`foo`时，其全名是`bar.foo`。以下命令`open bar` *打开*命名空间，这使我们可以使用较短的名称`foo`。为了避免名称冲突导致的错误，在下一个例子中，我们将我们的库定理版本放在一个新的叫做`MyRing`的命名空间中。

下面的例子显示，我们不需要`add_zero`或`add_right_neg`作为环的公理，因为它们可以从其他公理得出。

```
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing
```

结果是我们可以临时重新证明库中的一个定理，然后继续使用该库版本。但不要作弊！在接下来的练习中，请注意只使用我们在本节前面证明过的关于环的一般事实。

（如果您小心关注，您可能会注意到我们将`(R：Type*)`中的圆括号改为`{R：Type*}`的大括号。这声明`R`是一个*隐式参数*。我们将在一会儿解释这是什么意思，但现在不用担心）

这是一个有用的定理：

```
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]
```

证明配套版本：

```
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry
```

使用它们来证明以下内容：

```
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
```

有足够的计划，您只需三次重写就可以完成它们。

我们将现在解释花括号的用法。假设您在上下文中有`a`，`b`和`c`，以及一个假设`h：a + b = a + c`，您希望得出结论`b = c`。在Lean中，您可以按照应用它们到物体的同一种方式将定理应用于假说和事实，因此您可能认为`add_left_cancel a b c h`是事实`b = c`的证明。但是请注意，显式写出`a`，`b`和`c`是多余的，因为假设`h`清楚地表明这些是我们所考虑的对象。在这种情况下，输几个额外的字符并不麻烦，但是如果我们想应用`add_left_cancel`到更复杂的表达式，编写它们将是乏味的。在这样的情况下，Lean允许我们将参数标记为*隐式*，这意味着它们应被遗漏并通过其他方式（例如后续参数和假说）推断出来。`{a b c：R}`中的花括号正是这样。因此，只需给出定理的声明，正确的表达式就是`add_left_cancel h`。

为了举例说明，让我们展示`a * 0 = 0`如何从环公理中得出。

```
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]
```

我们使用了新的技巧！如果您通过证明，可以看到发生了什么。`have`策略引入了一个新的目标，`a * 0 + a * 0 = a * 0 + 0`，其上下文与原始目标相同。下一行的缩进表示Lean期望一个块策略，用于证明这个新的目标。因此，缩进促进了证明的模块化风格：缩进的子证明建立了由`have`引入的目标。之后，我们又回到证明原始目标，除了添加了一个新的假设`h`：证明过后，我们现在随时可以使用它。此时，目标正好是`add_left_cancel h`的结果。

我们也可以很好地关闭证明以`apply add_left_cancel h`或`exact add_left_cancel h`。`exact`策略接收一个证明项作为参数，该证明项完全证明了当前目标，而没有创建任何新的目标。`apply`策略是一种变体，其参数不一定是完整的证明。缺失的部分要么由Lean自动推断出来，要么成为需要证明的新目标。虽然`exact`策略在技术上是多余的，因为它的功能比`apply`少，但它使证明脚本对人类读者稍微清晰一些，且在库演变时更容易维护。

记住，乘法不一定是交换的，所以下面的定理也需要一些工作。

```
theorem zero_mul (a : R) : 0 * a = 0 := by
  sorry
```

到目前为止，你应该已经能够在接下来的练习中用证明替换每个`sorry`，只用我们在本节中已经建立的关于环的事实。

```
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry
```

在第三个定理中，我们不得不使用注解`(-0 : R)`代替`0`，因为如果不指定`R`，对Lean来说很难推断出我们心中的`0`是什么，而默认情况下它会被解释为一个自然数。

在Lean中，环中的减法可以被证明等于加上相加的逆。

```
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
```

对于实数，就是这样*定义*的：

```
example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl
```

证明项`rfl`是“反射性”的缩写。将它作为`a - b = a + -b`的证明，会迫使Lean展开定义并认出两边是相同的。`rfl`策略也是如此。这是Lean底层逻辑中所谓的*定义性等式*的一个实例。这意味着人们不仅可以用`sub_eq_add_neg`进行重写以替换`a - b = a + -b`，而且在某些情况下，当处理实数时，你可以交替使用等式的两边。例如，你现在已有足够的信息来证明上一节中的`self_sub`定理：

```
theorem self_sub (a : R) : a - a = 0 := by
  sorry
```

展示你可以用`rw`证明这一点，但是如果你将任意环`R`替换为实数，你也可以使用`apply`或`exact`来证明它。

Lean知道`1 + 1 = 2`在任何环中都成立。你可以花一点努力，用这个来证明上一节的`two_mul`定理：

```
theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  sorry
```

我们以查看我们以上所确定的有关加法和取反的事实没有需要环公理的全部强度，甚至是加法的交换性来结束这一节。一个更弱的概念，一个*群*，可以如下刻画：

```
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)
```

当群操作是可交换的时，人们通常使用加法表示，否则使用乘法表示。所以Lean定义了一个乘性版本以及加性版本（以及他们的阿贝尔变种，`AddCommGroup`和`CommGroup`）。

```
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)
```

如果你感到自信，试着只使用这些公理来证明下面的群的事实。你将需要在这过程中证明一些辅助性引理。我们在这一节中进行的证明提供了一些线索。

```
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  sorry

theorem mul_one (a : G) : a * 1 = a := by
  sorry

theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  sorry
```

显式调用这些引理是繁琐的，所以Mathlib提供了类似于ring的策略来覆盖大多数用途：*group*是用于非交换乘法群，*abel*是用于交换加法群，而*noncomm_ring*是用于非交换环。可能看起来奇怪，代数结构被称为*Ring*和*CommRing*，而策略却被命名为*noncomm_ring*和*ring*。这部分是由于历史原因，但也是为了给更常用的，处理交换环的策略带来更方便的短名称。

## 2.3.  Using Theorems and Lemmas

重写很适合用来证明等式，但是其他类型的定理该怎么证明呢？例如，我们如何证明一个不等式，比如当 $b\leq c$时，$a+e^{b}\leq a+e^{c}$ 总是成立的事实？我们已经看到，定理可以应用于参数和假设，并且 `apply` 和 `exact` 指令可以用来解决目标。在这一节，我们将充分利用这些工具。

考虑库定理 `le_refl` 和 `le_trans`：

```
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
```

如选有[第3.1节](C03_Logic.md#31-Implication-and-the-Universal-Quantifier) 中更详细的解释，`le_trans` 语句中的隐式括号向右关联，所以它应该被解释为 `a ≤ b → (b ≤ c → a ≤ c)`。库的设计者已经把 `le_trans` 的参数 `a`、`b` 和 `c` 设置为隐式，因此 Lean *不*会让你显式提供它们（除非你真的坚持这样做，我们稍后会讨论此问题）。相反，它希望从使用它们的上下文中推断它们。例如，当假设 `h : a ≤ b` 和 `h' : b ≤ c` 在上下文中时，以下都能正常工作：

```
variable (h : a ≤ b) (h' : b ≤ c)

#check (le_refl : ∀ a : Real, a ≤ a)
#check (le_refl a : a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (le_trans h : b ≤ c → a ≤ c)
#check (le_trans h h' : a ≤ c)
```

`apply` 指令接收一个普通语句或含义的证明，试图将结论与当前目标匹配，并将假设（如果有的话）留作新的目标。如果给定的证明与目标完全匹配（模 *定义* 等价），你可以使用 `exact` 指令代替 `apply`。所以，所有这些都可以工作：

```
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans
  · apply h₀
  . apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

example (x : ℝ) : x ≤ x :=
  le_refl x
```

在第一个示例中，应用 `le_trans` 创建了两个目标，我们使用点号来指示每个证明的开始。点号是可选的，但它们用来 *聚焦* 目标：在由点号引导的块内，只有一个目标是可见的，且必须在块结束之前完成。这里我们通过开始另一个新的块来结束第一个块。我们也可以简单的减少缩进。在第四个示例和最后一个示例中，我们完全避免进入策略模式：`le_trans h₀ h₁` 和 `le_refl x` 是我们需要的证明项。

这里还有一些库中的定理：

```
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
```

利用它们和 `apply` 以及 `exact` 证明以下内容：

```
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
```

事实上，Lean 有一个策略可以自动完成这种类型的事情：

```
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
```

`linarith` 策略就是设计来处理 *线性算法* 的。

```
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
```

除了上下文中的等式和不等式，`linarith` 还会使用你作为参数传递的额外不等式。在下一个示例中，`exp_le_exp.mpr h'` 是 `exp b ≤ exp c` 的证明，我们将在一会儿解释。注意，在 Lean 中，我们写 `f x` 来表示函数 `f` 应用于参数 `x`，就像我们写 `h x` 来表示将事实或定理 `h` 应用于参数 `x` 的结果一样。只有在复合参数如 `f (x + y)` 中才需要括号。没有括号，`f x + y` 将被解析为 `(f x) + y`。

```
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']
```

这里还有一些在库中可以用来建立实数上的不等式的定理。

```
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → 0 < b → (log a ≤ log b ↔ a ≤ b))
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
#check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
#check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
#check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
#check (add_pos : 0 < a → 0 < b → 0 < a + b)
#check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
#check add_le_add_left
```

某些定理，`exp_le_exp`，`exp_lt_exp`和 `log_le_log` 使用了*双向蕴含关系*，代表着“当且仅当”。（您可以在VS Code中通过`\lr` 或 `\iff`键入。）我们将在下一章中详细讨论此关系。这样的定理可以与`rw`一起使用，以将目标改写为等价的另一个目标：

```
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h
```

但是，在此部分中，我们将使用这样一个事实，即如果`h：A↔B`是这样的等价关系，那么`h.mp`确定了前向方向，`A→B`，而`h.mpr`确定了相反的方向，`B→A`。在这里，mp表示`modus ponens`，mpr代表`modus ponens reverse`。您也可以如果你偏好，你也可以使用`h.1`和`h.2`分别代替`h.mp`和`h.mpr`。因此，以下证明有效：

```
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl
```

第一行，应用`add_lt_add_of_lt_of_le`，创建了两个目标，然后我们再次使用一个点来分开对第一种证明和对第二种证明的证明。

尝试以下自己的示例。中间的例子向您展示了`norm_num`策略可以用来解决具体的数值目标。

```
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  have h₁ : 0 < 1 + exp b := by sorry
  apply (log_le_log h₀ h₁).mpr
  sorry
```

从这些例子中，明显能够找到您需要的库定理是形式化的重要组成部分。您可以使用以下策略：

- 您可以浏览其在[GitHub 仓库](https://github.com/leanprover-community/mathlib4)中的Mathlib。
- 您可以使用Mathlib [网页](https://leanprover-community.github.io/mathlib4_docs/)上的API文档。
- 您可以依赖于Mathlib的命名惯例和编辑器中的Ctrl-space补全，以猜测一个定理名（或在Mac键盘上使用Cmd-space）。在Lean中，一个名为`A_of_B_of_C`的定理，它从形如`B`和`C`的假设中建立形如`A`的东西，其中`A`，`B`和`C`近似我们可能大声朗读的目标。因此，建立形如`x + y ≤ ...`的定理可能会以`add_le`开始。键入`add_le`并按Ctrl-space将给你一些旁的选择。注意两次按下Ctrl-space将显示关于可用补全的更多信息。
- 如果您在VS Code中右键单击现有的定理名称，编辑器将显示一个菜单，其中具有跳转到定义定理的文件的选项，并且您可以找到附近的类似定理。
- 您可以使用`apply?`策略，该策略试图在库中找到相关的定理。

```
example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a
```

在此示例中尝试`apply?`，删除`exact`命令，然后取消注释上一行。使用这些技巧，看看你能否找到需要做下一个示例的内容：

```
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry
```

使用相同的技巧，确认`linarith`而不是`apply?`也可以完成任务。

这是不等式的另一个例子：
```
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg

  calc
    2 * a * b = 2 * a * b + 0 := by ring
    _ ≤ 2 * a * b + (a ^ 2 - 2 * a * b + b ^ 2) :=
      add_le_add (le_refl _) h
    _ = a ^ 2 + b ^ 2 := by ring
```

Mathlib 倾向在二元操作符如`*`与`^`两侧添加空格，但在这个例子中，更紧凑的格式增加了可读性。有一些值得注意的事情。首先，表达式`s ≥ t`在定义上等同于`t ≤ s`。原则上，这意味着我们应该能够互换使用它们。但是，Lean 的一些自动化操作不会识别这种等价，因此 Mathlib 倾向于更多地使用`≤` 而不是 `≥`。其次，我们广泛使用了`ring`策略，它真是节省了很多时间！最后，注意在第二个`calc`证明的第二行，我们可以简单地写出证明项`add_le_add (le_refl _) h`，而不是写作`by exact add_le_add (le_refl _) h`。

事实上，在上述证明中唯一的机智之处在于找出假设`h`。一旦我们有它，第二个计算仅包含线性算术，而`linarith`可以处理它：
```
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith
```

太棒了！我们挑战你使用这些思想来证明以下定理。你可以使用定理`abs_le'.mpr`。你还需要`constructor`策略将连接到两个目标；请参见[第3.4节](C03_Logic.md#34-Conjunction-and-Iff)。

```
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  sorry

#check abs_le'.mpr
```

如果你成功解决了这个问题，恭喜！你正走在成为大师级formalizer的道路上。

## 2.4.  More examples using apply and rw

实数上的`min`函数由以下三个事实唯一地表征：

```
#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
```

你能猜到以类似方式描述`max`的定理的名称吗？

请注意，我们必须通过写`min a b`而不是`min (a, b)`将`min`应用到一对参数`a`和`b`。在形式上，`min`是类型`ℝ → ℝ → ℝ` 的函数。当我们使用多个箭头编写这样的类型时，约定是隐含的括号关联到右边，所以类型被解释为`ℝ → (ℝ → ℝ)`。因此，如果`a`和`b`有类型`ℝ`那么`min a`有类型`ℝ → ℝ`，`min a b`有类型`ℝ`，所以`min`像一个具有两个参数的函数，如我们期望的那样。这种处理多个参数的方式被称为*柯理化*，得名于逻辑学家哈斯凯尔·柯里。

习惯 Lean 的运算顺序也需要一段时间。函数应用在中缀操作中绑定得更紧密，因此表达式`min a b + c`被解释为`(min a b) + c`。随着时间的推移，这些规约将变得熟悉起来。

使用定理`le_antisymm`，我们可以证明如果两个实数都小于或等于另一个，那么它们就相等。使用上述的事实和这一事实，我们可以证明`min`是可交换的：

```
example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    · apply min_le_right
    apply min_le_left
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left
```

在这里，我们使用了点来分隔不同目标的证明，我们的用法并不一致：在外层，我们为两个目标使用点和缩进，而对于嵌套的证明，我们只在单一目标存在时使用点。这两种规定都是合理和有用的。我们还使用`show`策略来组织证明并指示在每个块中正在证明什么。无需`show`命令，证明仍然有效，但使用它们使得证明更容易阅读和维护。

重复的证明可能会让你感到困扰。预示你将来会学到的技能，我们注意到避免重复的一个方式是陈述一个局部引理然后使用它：

```
example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min
    apply min_le_right
    apply min_le_left
  apply le_antisymm
  apply h
  apply h
```

我们会在[第3.1节](C03_Logic.md#31-Implication-and-the-Universal-Quantifier)更多地讨论全称量词，但是这里足够说出假设`h`，
这说明任何x和y的期望不等式都成立，并且`intro`策略引入任意的`x`和`y`以建立结论。在`le_antisymm`之后的第一个`apply`被隐含地使用`h a b`，而第二个使用`h b a`。

另一种解决方案是使用`repeat`策略，它可以尽可能多地应用策略（或块）。

```
example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left
```

无论是否使用这些技巧，我们都鼓励你证明以下内容：

```
example : max a b = max b a := by
  sorry
example : min (min a b) c = min a (min b c) := by
  sorry
```

当然，我们也欢迎你证明`max`的结合性。

一个有趣的事实是，`min`像乘法分配加法那样分配`max`，反之亦然。换句话说，在实数上，我们有标识`min a (max b c) ≤ max (min a b) (min a c)`以及与`max`和`min`切换的对应版本。但是在下一节我们将看到，这并不是由于`≤`的传递性和自反性，以及`min`和`max`的上述特性。我们需要使用事实，`≤`在实数上是一个*total order*，也就是说，它满足`∀ x y, x ≤ y ∨ y ≤ x`。在这里，析取符号，`∨`,代表“或者”。在第一种情况下，我们有`min x y = x`,在第二种情况下，我们有`min x y = y`。我们将在[3.5节](C03_Logic.md#35-Disjunction)学习如何通过案例推理，但现在我们将坚持不需要案例分割的例子。

这是其中一个例子：

```
theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  sorry
example : min a b + c = min (a + c) (b + c) := by
  sorry
```
很明显，`aux`提供了证明等式所需的两个不等式之一，但将适合的值应用于它也能得到另一个方向。作为提示，你可以使用定理`add_neg_cancel_right`和`linarith`策略。

Lean的命名规则在库的三角不等式名称中得以体现：

```
#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)
```

用它来证明以下变体：
```
example : |a| - |b| ≤ |a - b| :=
  sorry
end
```

看看你能否在三行或更少的行数内做到这一点。您可以使用定理`sub_add_cancel`。

我们将在接下来的几节中使用的另一个重要的关系是自然数上的可分性关系，`x ∣ y`。小心：可分性符号*不是*你键盘上的普通条。相反，它是通过在VS Code中输入`\ |`而获得的unicode字符。按惯例，Mathlib在定理名称中使用`dvd`来指代它。

```
example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
   apply dvd_mul_left
```

在最后一个例子中，指数是一个自然数，并且应用 `dvd_mul_left`使 Lean 将 `x^2`的定义扩展为`x * x^1`。看看你能否猜到你需要证明下面的定理的名字：

```
example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  sorry
end
```

与可分性相比，*最大公约数*，`gcd`，和最小公倍数，`lcm`，类似于`min`和`max`。由于每个数都可以除以`0`，`0`正是在可分性方面的最大元素：

```
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)
```

看看你能否猜到你将需要证明以下内容的定理名称：

```
example : Nat.gcd m n = Nat.gcd n m := by
  sorry
```

提示：你可以使用`dvd_antisymm`，但如果你这样做，Lean会抱怨表达式在通用定理和`Nat.dvd_antisymm`版本之间的模糊，后者是专门针对自然数的。你可以使用`_root_.dvd_antisymm`来指定通用的一个；两者均可工作。

## 2.5.  Proving Facts about Algebraic Structures

在[2.2节](C02_Basics.md#22-Proving-Identities-in-Algebraic-Structures)中，我们看到，许多关于实数的常见恒等式在更通用的代数结构类，比如交换环，中也成立。我们可以使用任何我们想要描述的代数结构的公理，而不仅仅是等式。例如，*偏序*由一个具有二元关系的集合组成，该二元关系是自反的和传递的，例如实数上的`≤`。Lean知道关于偏序的信息：

```
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
```

在此，我们应用的是Mathlib的惯例，使用像`α`、`β`和`γ`（输入`\a`、`\b`和`\g`）的字母代表任意类型。 库通常会使用像`R`和`G`这样的字母来表示像环和群这样的代数结构的携带，但是当与之关联的结构很少或者没有时，通常使用希腊字母代表类型。

与任何偏序`≤`相关联的还有一个*严格偏序*`<`，它的作用有点类似实数上的`<`。说`x`在此顺序下小于`y`等价于说它小于或等于`y`且不等于`y`。

```
#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne
```

在此示例中，符号`∧`表示“和”，符号`¬`表示“非”，`x ≠ y`缩写为`¬（x = y）`。在[第三章](C03_Logic.md#3-Logic)，你将学习如何使用这些逻辑连接词*证明*`<`具有所示的属性。

*格*是扩展了偏序并且具有与实数上的`min`和`max`相类似的操作`⊓`和`⊔`的结构：

```
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
```

`⊓`和`⊔`的特性使我们称它们为*greatest lower bound*和*least upper bound*。您可以在VS代码中使用`\glb`和`\lub`输入它们。这些符号也经常被称为*infimum*和*supremum*，Mathlib在定理名中也引用它们作为`inf`和`sup`。为了进一步复杂化，他们也经常被称为*meet*和*join*。因此，如果您使用格，您必须记住以下的对应关系：

- `⊓`是*greatest lower bound*，*infimum*或*meet*。
- `⊔`是*least upper bound*，*supremum*或*join*。

格的一些实例包括：

- 对任何total order上的`min`和`max`，如整数或带有`≤`的实数
- 对某个域的子集集合上的`∩`和`∪`，伴随着`⊆`的排序
- 对布尔真值上的`∧`和`∨`，如果`x`是假的或者`y`是真的，那么排序为`x ≤ y`
- 对自然数（或正自然数）上的`gcd`和`lcm`，以及divisibility ordering，`∣`
- 向量空间的线性子空间的集合，其中最大下界由两个空间的交集给出，最小上界由两个空间的和给出，排序为包含
- 集合的拓扑结构的集合（或者在Lean中，一个类型），其中两个拓扑的最大下界由它们的并集生成的拓扑，最小上界是它们的交集，排序为反向包含

您可以检查，像`min` / `max`和`gcd` / `lcm`，你可以仅使用他们的特性公理，加上`le_refl` 和 `le_trans`，来证明infimum 和 supremum 的交换性和结合性。

```
example : x ⊓ y = y ⊓ x := by
  sorry

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  sorry

example : x ⊔ y = y ⊔ x := by
  sorry

example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  sorry
```

在Mathlib中，这些定理分别被记为`inf_comm`，`inf_assoc`，`sup_comm`和`sup_assoc`。

另一个好的练习是仅使用公理来证明*吸收定律*：

```
theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  sorry

theorem absorb2 : x ⊔ x ⊓ y = x := by
  sorry
```

这些可以在Mathlib上找到，名字分别是`inf_sup_self`和`sup_inf_self`。

满足附加等式`x ⊓ (y ⊔ z) = (x ⊓ y) ⊔ (x ⊓ z)` 和 `x ⊔ (y ⊓ z) = (x ⊔ y) ⊓ (x ⊔ z)`的格被称为*distributive lattice*。Lean也知道这些：

```
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
```

左版本和右版本在`⊓`和`⊔`的交换性下可以很容易地证明是等价的。提供一个具有有限多个元素的非分布格的明确描述，以展示不是所有的格都是分布的，这是一个很好的练习。此外，展示在任何格中，分配律的任一方都暗示了另一方，也是一个很好的练习：

```
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry
```

将公理结构组合成更大的结构是可能的。例如，一个 *strict ordered ring* 是一个具有partial order的交换环，满足额外的公理，这些公理表明环运算与序兼容：

```
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)
```

[第3章](C03_Logic.md#3-Logic) 将提供从 `mul_pos` 和 `<` 的定义中导出以下内容的方法：

```
#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
```

然后，一个扩展的练习是证明许多用来推理算术和实数上的序的常用事实，对于任何有序环都通用。这里有几个你可以尝试的例子，只使用环、partial order和最后两个例子中列举的事实：
```
example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry
```

最后，这是最后一个例子。一个 *度量空间* 是一个带有距离概念的集合，`dist x y`将任何一对元素映射到一个实数。距离函数被假设满足以下公理：

```
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)
```

掌握了本节后，你可以证明从这些公理中可以得出距离总是非负的：

```
example (x y : X) : 0 ≤ dist x y := by
  sorry
```

我们建议利用定理 `nonneg_of_mul_nonneg_left`。你可能已经猜到，这个定理在 Mathlib 中被称为 `dist_nonneg`。
