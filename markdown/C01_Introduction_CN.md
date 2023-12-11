# 1.  Introduction

## 1.1.  Getting Started

The goal of this book is to teach you to formalize mathematics using the Lean 4 interactive proof assistant. It assumes that you know some mathematics, but it does not require much. Although we will cover examples ranging from number theory to measure theory and analysis, we will focus on elementary aspects of those fields, in the hopes that if they are not familiar to you, you can pick them up as you go. We also don’t presuppose any background with formal methods. Formalization can be seen as a kind of computer programming: we will write mathematical definitions, theorems, and proofs in a regimented language, like a programming language, that Lean can understand. In return, Lean provides feedback and information, interprets expressions and guarantees that they are well-formed, and ultimately certifies the correctness of our proofs.

这本书的目标是教你使用Lean 4交互式证明助手来形式化数学。它假设你知道一些数学，但不需要太多。尽管我们将涵盖从数论到测度理论和分析的例子，但我们将重点关注这些领域的基础方面，希望如果你对它们不熟悉，你可以在进行中掌握它们。我们也不预设任何与形式方法有关的背景知识。形式化可以被看作是一种计算机编程：我们将以一个规范语言（类似于编程语言）写出数学定义、定理和证明，让Lean能够理解。作为回报，Lean提供反馈和信息，解释表达并保证它们格式正确，并最终验证我们的证明是否正确。

You can learn more about Lean from the [Lean project page](https://leanprover.github.io/) and the [Lean community web pages](https://leanprover-community.github.io/). This tutorial is based on Lean’s large and ever-growing library, *Mathlib*. We also strongly recommend joining the [Lean Zulip online chat group](https://leanprover.zulipchat.com/) if you haven’t already. You’ll find a lively and welcoming community of Lean enthusiasts there, happy to answer questions and offer moral support.

您可以从[Lean项目页面](https://leanprover.github.io/)和[Lean社区网页](https://leanprover-community.github.io/)了解更多关于Lean的信息。本教程基于Lean庞大且不断增长的库，*Mathlib*。如果您还没有加入，我们强烈推荐您加入[Lean Zulip在线聊天组](https://leanprover.zulipchat.com/)。在那里，你会发现一个活跃而热情的Lean爱好者社区，他们乐于回答问题并提供道义支持。

Although you can read a pdf or html version of this book online, it designed to be read interactively, running Lean from inside the VS Code editor. To get started:

尽管你可以在线阅读这本书的pdf或html版本，但它是设计为在VS Code编辑器内部交互式运行Lean并进行阅读的。开始如下：

1. Install Lean 4 and VS Code following these [installation instructions](https://leanprover-community.github.io/get_started.html).
2. Make sure you have [git](https://git-scm.com/) installed.
3. Follow these [instructions](https://leanprover-community.github.io/install/project.html#working-on-an-existing-project) to fetch the `mathematics_in_lean` repository and open it up in VS Code.
4. Each section in this book has an associated Lean file with examples and exercises. You can find them in the folder `MIL`, organized by chapter. We strongly recommend making a copy of that folder and experimenting and doing the exercises in that copy. This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below). You can call the copy `my_files` or whatever you want and use it to create your own Lean files as well.

At that point, you can open the textbook in a side panel in VS Code as follows:

在那个时候，你可以按照以下方式在VS Code的侧面面板中打开教科书：

1. Type `ctrl-shift-P` (`command-shift-P` in macOS).
2. Type `Lean 4: Open Documentation View` in the bar that appears, and then press return. (You can press return to select it as soon as it is highlighted in the menu.)
3. In the window that opens, click on `Open documentation of current project`.

Alternatively, you can run Lean and VS Code in the cloud, using [Gitpod](https://gitpod.io/). You can find instructions as to how to do that on the Mathematics in Lean [project page](https://github.com/leanprover-community/mathematics_in_lean) on Github. We still recommend working in a copy of the MIL folder, as described above.

或者，您可以在云端运行Lean和VS Code，使用[Gitpod](https://gitpod.io/)。您可以在Github上的Mathematics in Lean [项目页面](https://github.com/leanprover-community/mathematics_in_lean) 找到如何操作的指南。我们仍然建议您在MIL文件夹的副本中工作，如上述所描述。

This textbook and the associated repository are still a work in progress. You can update the repository by typing `git pull` followed by `lake exe cache get` inside the `mathematics_in_lean` folder. (This assumes that you have not changed the contents of the MIL folder, which is why we suggested making a copy.)

这本教科书和相关的仓库仍在进行中。您可以通过在`mathematics_in_lean`文件夹内输入`git pull`，然后跟上`lake exe cache get`来更新仓库。（这假设您没有更改MIL文件夹的内容，这就是我们建议制作副本的原因。）

We intend for you to work on the exercises in the `MIL` folder while reading the textbook, which contains explanations, instructions, and hints. The text will often include examples, like this one:

我们希望你在阅读教科书的同时，处理`MIL`文件夹中的练习。这本教科书包含了解释、指导和提示。文本经常会包括一些例子，就像这个：

```
  #eval "Hello, World!"
```

You should be able to find the corresponding example in the associated Lean file. If you click on the line, VS Code will show you Lean’s feedback in the `Lean Goal` window, and if you hover your cursor over the `#eval` command VS Code will show you Lean’s response to this command in a pop-up window. You are encouraged to edit the file and try examples of your own.

你应该能在关联的Lean文件中找到对应的示例。如果你点击这行，VS Code会在`Lean Goal`窗口中显示Lean的反馈，如果你将光标悬停在`#eval`命令上，VS Code会在弹出窗口中显示Lean对此命令的响应。鼓励你编辑文件并尝试自己的示例。

This book moreover provides lots of challenging exercises for you to try. Don’t rush past these! Lean is about *doing* mathematics interactively, not just reading about it. Working through the exercises is central to the experience. You don’t have to do all of them; when you feel comfortable that you have mastered the relevant skills, feel free to move on. You can always compare your solutions to the ones in the `solutions` folder associated with each section.

这本书还提供了许多具有挑战性的练习供你尝试。不要匆忙跳过这些！Lean 是关于*做*数学的互动方式，而不仅仅是阅读它。通过练习来进行学习是核心体验。你并不需要完成所有的练习；当你感觉自己已经掌握了相关技能时，就可以随意前进了。你总是可以将自己的解答与每个章节附带的`solutions`文件夹中的解答进行比较。

## 1.2.  Overview

Put simply, Lean is a tool for building complex expressions in a formal language known as *dependent type theory*.

简单来说，Lean是一个用于在被称为*依赖类型理论*的正式语言中构建复杂表达式的工具。

Every expression has a *type*, and you can use the *#check* command to print it. Some expressions have types like *ℕ* or *ℕ → ℕ*. These are mathematical objects.

每个表达式都有一个*类型*，你可以使用*#check* 命令来打印它。一些表达式的类型像是*ℕ*或者是*ℕ → ℕ*。这些都是数学对象。

```
  #check 2 + 2
  
  def f (x : ℕ) :=
    x + 3
    
  #check f
```

Some expressions have type `Prop`. These are mathematical statements.

一些表达式的类型为`Prop`。这些是数学陈述。

```
  #check 2 + 2 = 4
  
  def FermatLastTheorem :=
    ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n
  
  #check FermatLastTheorem
```

Some expressions have a type, *P*, where *P* itself has type *Prop*. Such an expression is a proof of the proposition *P*.

一些表达式有一个类型*P*，其中*P*本身的类型是*Prop*。这样的表达式就是命题*P*的证明。

```
  theorem easy : 2 + 2 = 4 :=
    rfl
    
  #check easy
  
  theorem hard : FermatLastTheorem :=
    sorry
  
  #check hard
```

If you manage to construct an expression of type `FermatLastTheorem` and Lean accepts it as a term of that type, you have done something very impressive. (Using `sorry` is cheating, and Lean knows it.) So now you know the game. All that is left to learn are the rules.

如果你成功构建了一个类型为`FermatLastTheorem`的表达式，并且Lean接受它作为该类型的项，那么你已经做得非常出色。（使用`sorry`是作弊，Lean知道这一点。）所以现在你知道这个游戏。剩下要学习的只有规则了。

This book is complementary to a companion tutorial, [Theorem Proving in Lean](https://leanprover.github.io/theorem_proving_in_lean4/), which provides a more thorough introduction to the underlying logical framework and core syntax of Lean. *Theorem Proving in Lean* is for people who prefer to read a user manual cover to cover before using a new dishwasher. If you are the kind of person who prefers to hit the *start* button and figure out how to activate the potscrubber feature later, it makes more sense to start here and refer back to *Theorem Proving in Lean* as necessary.

这本书是对配套教程的补充，[Lean中的定理证明](https://leanprover.github.io/theorem_proving_in_lean4/)，它提供了更深入的介绍关于Lean底层逻辑框架和核心语法。*Lean中的定理证明* 是为那些喜欢在使用新洗碗机之前从头到尾阅读用户手册的人准备的。如果你是那种喜欢先按*开始*按钮，然后再搞清楚如何启动锅刷功能的人，那么从这里开始并在必要时参考 *Lean中的定理证明*会更有意义。

Another thing that distinguishes *Mathematics in Lean* from *Theorem Proving in Lean* is that here we place a much greater emphasis on the use of *tactics*. Given that we are trying to build complex expressions, Lean offers two ways of going about it: we can write down the expressions themselves (that is, suitable text descriptions thereof), or we can provide Lean with *instructions* as to how to construct them. For example, the following expression represents a proof of the fact that if `n` is even then so is `m * n`:

另一件区别于*Theorem Proving in Lean*的事情是，在*Mathematics in Lean*中我们更加强调使用*tactics*。鉴于我们试图构建复杂的表达式，Lean提供了两种方法：我们可以写下表达式本身（即适当的文字描述），或者我们可以向Lean提供如何构造它们的*指示*。例如，以下表达式代表了一个证明：如果`n`是偶数，则`m * n`也是偶数。

```
  example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
    have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
    show ∃ l, m * n = l + l from ⟨_, hmn⟩
```

The *proof term* can be compressed to a single line:

*证明项*可以压缩为一行：

```
  example : ∀ m n : Nat, Even n → Even (m * n) :=
  fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩
```

The following is, instead, a *tactic-style* proof of the same theorem, where lines starting with `--` are comments, hence ignored by Lean:

以下是同一定理的*策略式*证明，以`--`开头的行是注释，因此被Lean忽视：

```
  example : ∀ m n : Nat, Even n → Even (m * n) := by
    -- Say m and n are natural numbers, and assume n=2*k.
    rintro m n ⟨k, hk⟩
    -- We need to prove m*n is twice a natural number. Let's show it's twice m*k.
    use m * k
    -- Substitute for n,
    rw [hk]
    -- and now it's obvious.
    ring
```

As you enter each line of such a proof in VS Code, Lean displays the *proof state* in a separate window, telling you what facts you have already established and what tasks remain to prove your theorem. You can replay the proof by stepping through the lines, since Lean will continue to show you the state of the proof at the point where the cursor is. In this example, you will then see that the first line of the proof introduces `m` and `n` (we could have renamed them at that point, if we wanted to), and also decomposes the hypothesis `Even n` to a `k` and the assumption that `n = 2 * k`. The second line, `use m * k`, declares that we are going to show that `m * n` is even by showing `m * n = 2 * (m * k)`. The next line uses the `rewrite` tactic to replace `n` by `2 * k` in the goal, and the `ring` tactic solves the resulting goal `m * (2 * k) = 2 * (m * k)`.

当你在VS Code中输入这样一个证明的每一行时，Lean会在另一个窗口中显示*证明状态*，告诉你已经确定了哪些事实以及还需要完成什么任务来证明你的定理。你可以通过逐行查看来回放证明过程，因为Lean将继续向你展示光标所在位置处的证明状态。在这个例子中，你会看到证明的第一行引入了`m`和`n`(如果我们想要，那时就可以重命名它们)，并且也分解了假设`Even n`为一个`k`和假设 `n = 2 * k`. 第二行, `use m * k`, 声称我们将通过展示 `m * n = 2 * (m * k)` 来表明 `m * n` 是偶数. 下一行使用 `rewrite` 策略替换目标中的 `n`, 并用 `ring` 策略解决结果目标 `m *(2*k) = 2*(m*k)`.

The ability to build a proof in small steps with incremental feedback is extremely powerful. For that reason, tactic proofs are often easier and quicker to write than proof terms. There isn’t a sharp distinction between the two: tactic proofs can be inserted in proof terms, as we did with the phrase `by rw [hk, mul_left_comm]` in the example above. We will also see that, conversely, it is often useful to insert a short proof term in the middle of a tactic proof. That said, in this book, our emphasis will be on the use of tactics.

以小步骤构建证明并获得增量反馈的能力极其强大。因此，策略证明通常比证明术语更容易且更快地编写。两者之间并没有明显的区别：我们可以在证明术语中插入策略性的证据，就像我们在上面的例子中使用`by rw [hk, mul_left_comm]`短语所做的那样。我们也将看到，相反地，在策略性证据中间插入一个简短的证据术语往往是有用的。尽管如此，在这本书中，我们将重点放在使用策略上。

In our example, the tactic proof can also be reduced to a one-liner:

在我们的示例中，策略证明也可以简化为一行代码：

```
  example : ∀ m n : Nat, Even n → Even (m * n) := by
    rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring
```

Here we have used tactics to carry out small proof steps. But they can also provide substantial automation, and justify longer calculations and bigger inferential steps. For example, we can invoke Lean’s simplifier with specific rules for simplifying statements about parity to prove our theorem automatically.

在这里，我们使用了策略来进行小的证明步骤。但是它们也可以提供大量的自动化，并为更长的计算和更大的推理步骤提供合理性。例如，我们可以调用Lean的简化器，使用特定规则来简化关于奇偶性声明以自动证明我们的定理。

```
  example : ∀ m n : Nat, Even n → Even (m * n) := by
    intros; simp [*, parity_simps]
```

Another big difference between the two introductions is that *Theorem Proving in Lean* depends only on core Lean and its built-in tactics, whereas *Mathematics in Lean* is built on top of Lean’s powerful and ever-growing library, *Mathlib*. As a result, we can show you how to use some of the mathematical objects and theorems in the library, and some of the very useful tactics. This book is not meant to be used as an complete overview of the library; the [community](https://leanprover-community.github.io/) web pages contain extensive documentation. Rather, our goal is to introduce you to the style of thinking that underlies that formalization, and point out basic entry points so that you are comfortable browsing the library and finding things on your own.

两个介绍之间的另一个大区别在于，《Lean中的定理证明》仅依赖于核心Lean及其内置策略，而《Lean中的数学》则建立在Lean强大且不断增长的库——Mathlib之上。因此，我们可以向您展示如何使用库中的一些数学对象和定理，以及一些非常有用的策略。这本书并不意味着要作为对库完整概述；[社区](https://leanprover-community.github.io/)网页包含了详尽文档。相反，我们的目标是向您介绍支撑那种形式化思考方式，并指出基础入口点，使您能够自如地浏览该库并自行查找所需内容。

Interactive theorem proving can be frustrating, and the learning curve is steep. But the Lean community is very welcoming to newcomers, and people are available on the [Lean Zulip chat group](https://leanprover.zulipchat.com/) round the clock to answer questions. We hope to see you there, and have no doubt that soon enough you, too, will be able to answer such questions and contribute to the development of *Mathlib*.

交互式定理证明可能会令人沮丧，学习曲线也很陡峭。但是Lean社区对新手非常欢迎，而且在[Lean Zulip聊天组](https://leanprover.zulipchat.com/)中总有人随时回答问题。我们希望能在那里见到你，并深信不久的将来，你也能够回答这样的问题并为*Mathlib*的开发做出贡献。

So here is your mission, should you choose to accept it: dive in, try the exercises, come to Zulip with questions, and have fun. But be forewarned: interactive theorem proving will challenge you to think about mathematics and mathematical reasoning in fundamentally new ways. Your life may never be the same.

所以，这是你的任务，如果你选择接受的话：深入研究，尝试练习题，有问题就去Zulip提问，并享受其中的乐趣。但请事先警告：交互式定理证明将挑战你以全新的方式思考数学和数学推理。你的生活可能永远不会再一样了。

*Acknowledgments.* We are grateful to Gabriel Ebner for setting up the infrastructure for running this tutorial in VS Code, and to Scott Morrison and Mario Carneiro for help porting it from Lean 4. We are also grateful for help and corrections from Julian Berman, Alex Best, Bulwi Cha, Bryan Gin-ge Chen, Mauricio Collaris, Johan Commelin, Mark Czubin, Denis Gorbachev, Winston de Greef, Mathieu Guay-Paquet, Julian Külshammer, Martin C. Martin, Giovanni Mascellani, Isaiah Mindich, Hunter Monroe, Pietro Monticone, Oliver Nash, Bartosz Piotrowski, Nicolas Rolland, Guilherme Silva, Floris van Doorn, and Eric Wieser. Our work has been partially supported by the Hoskinson Center for Formal Mathematics.

*致谢。*我们感谢Gabriel Ebner为在VS Code中运行此教程设置的基础设施，也感谢Scott Morrison和Mario Carneiro帮助我们将其从Lean 4移植过来。我们还要感谢Julian Berman、Alex Best、Bulwi Cha、Bryan Gin-ge Chen、Mauricio Collaris、Johan Commelin、Mark Czubin、Denis Gorbachev、Winston de Greef, Mathieu Guay-Paquet, Julian Külshammer, Martin C. Martin, Giovanni Mascellani, Isaiah Mindich, Hunter Monroe, Pietro Monticone, Oliver Nash, Bartosz Piotrowski，Nicolas Rolland，Guilherme Silva，Floris van Doorn以及Eric Wieser提供的帮助和修正。 我们的工作部分得到了Hoskinson Formal Mathematics Center的支持。

# 3.1. Implication and the Universal Quantifier
