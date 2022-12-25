# CSE203-Logic-and-Proof

## Explanation of the functions
---
### 1. Basic Notation for Data Type
```coq
Notation "[ 'seq' E | i < n ]" := (mkseq (fun i => E) n)
  (at level 0, E at level 99, i name,
   format "[ 'seq'  E  |  i  <  n ]") : seq_scope.
```
当使用"[ 'seq' E | i < n ]"的形式时，Coq会把它解释成调用函数"mkseq"，并传入两个参数:
- 一个函数，该函数的输入是i (i是一个自变量)，输出是E
- 一个数字n

对于0 <= i < n，生成一个序列`[E(0), E(1), E(2), ..., E(n-1)]`
- "at level 0"表示这个记法的优先级是0，也就是说它的优先级是最低的。 "E at level 99"表示E的优先级是99，也就是说E是最高优先级的
- "format"后面的字符串是这个记法的格式化字符串，它描述了记法的形式。在这个例子中，格式化字符串表示这个记法的形式是`[ 'seq' E | i < n ]`，其中E和n是可以替换的

```coq
Lemma mkseqS {T : Type} (f : nat -> T) (n : nat) :
  [seq f i | i < n.+1] = rcons [seq f i | i < n] (f n).
```
`rcons`是一个函数，它的作用是在一个序列的末尾添加一个元素。假设`f: nat -> nat`, $f(x)=x+1$, 这两个是等价的`[seq f i | i < 3.+1] = [f 0, f 1, f 2, f 3]`和`rcons [seq f i | i < 3] (f 3) = [f 0, f 1, f 2] ++ [f 3]`

```coq
Lemma divnE (n : nat) (p : nat) (k : nat) :
  p != 0 -> k * p <= n < k.+1 * p -> n %/ p = k.
```
计算整除的数字，逻辑如下
$$
k \cdot p \leq n < (k+1) \cdot p \Rightarrow n//p=k
$$
`%/`是coq中的整除计算符号

---
### 2. Discrete $\log_2(n)$ functions and lemma
```coq
Lemma log2_homo : {homo log2 : m n / m <= n}.
```
对于任意的数字m和n，如果$m \leq n$，那么有$\log_2 m \leq \log_2 n$。其中"homo"是一个Coq关键字，它表示"log2"是一个单射函数