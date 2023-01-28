#  Nim Game
This is the final project for CSE203 - Logic and Proof at Ecole Polytechnique. The project was finished by [Junyuan Wang](https://github.com/frank2002) and me, under the supervision from [Prof. Pierre-Yves Strub](http://www.strub.nu/) and [Prof. Benjamin Werner](http://www.lix.polytechnique.fr/Labo/Benjamin.Werner/). The project was finally defended under the supervision of [Prof. Pierre-Yves Strub](http://www.strub.nu/). You can find the code and slide from following link.

- [Code] - [link](https://github.com/yubocai-poly/Nim-Game/blob/main/Project/nim.v)
- [Slides] - [link](https://github.com/yubocai-poly/Nim-Game/blob/main/Project/CSE203_Final_Project.pdf)

## Introduction to the Project
Nim is a mathematical game of strategy in which two players take turns removing objects from distinct heaps or piles. For more information, you can access the [[wiki page]](https://en.wikipedia.org/wiki/Nim#Game_play_and_illustration) of nim game. The purpose of this project is to try to accomplish a formal proof of the winning strategy of the nim game through the **Coq** language. For more information about Nim Game's winning strategy you can visit the following [[link]](https://en.wikipedia.org/wiki/Nim#Mathematical_theory).

## Winning Strategy of Nim Game
In a normal Nim game, the player making the first move has a winning strategyu if and only if the nim-sum of the sizes of the heaps is not zero. Otherwise, the second player has a winning strategy. The winning strategy is to make the nim sum becomes 0 after each move.

Notice that the nim-sum $(\oplus)$ obeys the usual associative and commutative laws of addition (+) and also satisfies an additional property, $x \oplus x = 0$.

Let $x_1, \ldots, x_n$ be the sizes of the heaps before a move, and $y_1, \ldots, y_n$ the corresponding sizes after a move. Let $s=x_1 \oplus \ldots \oplus x_n$ and $t=y_1 \oplus \ldots \oplus y_n$. If the move was in heap $k$, we have $x_i=y_i$ for all $i \neq k$, and $x_k>y_k$. By the properties of $\oplus$ mentioned above, we have

```
    t = 0 ⊕ t
      = s ⊕ s ⊕ t
      = s ⊕ (x1 ⊕ ... ⊕ xn) ⊕ (y1 ⊕ ... ⊕ yn)
      = s ⊕ (x1 ⊕ y1) ⊕ ... ⊕ (xn ⊕ yn)
      = s ⊕ 0 ⊕ ... ⊕ 0 ⊕ (xk ⊕ yk) ⊕ 0 ⊕ ... ⊕ 0
      = s ⊕ xk ⊕ yk
 
(*) t = s ⊕ xk ⊕ yk.
```

Then, the theorem follows by induction on the length of the game from these two lemmas. Here we denote $s$ is the state before move and $t$ (or $s'$) is the state after move. Also, the number here means nim sum.

- **Lemma 1.** If $s=0$, then $t \neq 0$ no matter what move is going to have next. (**Lemma z2nz** in Coq)
- **Lemma 2.** If $s\neq 0$, there exist one move that make $t=0$. (**Lemma nz2z** in Coq)

## Structure of the code for project
- **Part 1.** Numberical Lemma on list, binary numbers and bxor operations...
- **Part 2.** Definition for state, rows, bijective relation...
- **Part 3.** Operations and Lemma on weights
- **Part 4.** Proof for **turn_weight**, **z2nz**, and **nz2z**

## Code for Operations and Lemma on weights
This part of code are operations and Lemma on weights, we prove by induction and operations in bxor.
```coq
Lemma weight_empty : weight (fun=> 0) = 0%:B.

Lemma weight_r0: weight_r nil = bits0.

Lemma weight_r1 (n : nat): weight_r [:: n] = n2b n.

Lemma weight_rS (n : nat) (ns : list nat) :
  weight_r (n :: ns) = n2b n .+ weight_r ns.

Lemma weight_rD (r s : list nat) :
  weight_r (r ++ s) = bxor (weight_r r) (weight_r s).
```

## Proof for z2nz
We apply contradiction to prove **z2nz** that if $s = 0$, then $t \neq 0$ no matter what move is made. 
```coq
Lemma z2nz (i : 'I_p) (s1 s2 : state) :
  R i s1 s2 -> weight s1 = 0%:B -> weight s2 <> 0%:B.
```
We need to prove other two Lemma where $x \oplus x=0$ and $\forall n \in \mathbb{N}, n < n, \rightarrow false$ in order to create contradiction.

```coq
Lemma b02bnbb (x : 'I_p) (s : state):
  0%:B = n2b (s x) .+ n2b (s x).
  
Lemma ltf (n : nat):
  n < n -> false.
```

We have **n2b_inj** that we can duduce that **s2 i = s1 i** which is contradiction with the assupmtion that **s2 i < s1 i**

## Proof for nz2z

We prove if $s \neq 0$, it is possible to make a move so that $s^{\prime}=0$ $\mathbf{n z 2 z}$ in following steps. We denote $x_1, \cdots, x_n$ is the number for each row before the move, $y_1, \cdots, y_n$ is the number for each row after the move

- $d$ be the position of leftmost nonzero bit in the binary representation of $s$ exists.
- Prove $\exists k$ such that $x_{k}[d] \neq 0$. We prove this by contradiction.
- We set $y_{k} = s \oplus x_k$ and assume $y_{k} < x_{k}$, then we prove $\forall i, d < i \rightarrow x_{k}=y_{k}$.
- Finish the prove with weight $s' = 0\%:B$ or R k s s'






