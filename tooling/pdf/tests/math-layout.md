# Mathematical layout regression

Public source examples for PDF layout.

Column pairs.

```math
\begin{aligned}
&\text{Forward }\mathop{\mathrm{Perm}}\nolimits:&&\text{Inverse }\mathop{\mathrm{Perm}}\nolimits^{-1}:\\
&L_0=X[0:128],\ R_0=X[128:256]&&L_{12}=Y[0:128],\ R_{12}=Y[128:256]\\
&\text{for }i=0,\ldots,11:&&\text{for }i=11,\ldots,0:\\
&\quad M_i=\mathop{\mathrm{RoundMask}}\nolimits(i,R_i)&&\quad R_i=L_{i+1}\\
&\quad L_{i+1}=R_i&&\quad M_i=\mathop{\mathrm{RoundMask}}\nolimits(i,R_i)\\
&\quad R_{i+1}=L_i\oplus M_i&&\quad L_i=R_{i+1}\oplus M_i\\
&Y=L_{12}\Vert R_{12}&&X=L_0\Vert R_0
\end{aligned}
```

Array rules.

```math
\begin{array}{c|c|c|l}
\text{Candidate words}&E&V&\text{Accept if}\\\hline
12&X_{\mathrm{candidate}}[0:128]&X_{\mathrm{candidate}}[128:256]&V=\mathop{\mathrm{Trunc}}\nolimits_{128}(\mathop{\mathrm{SHA256}}\nolimits(E))\\
15&X_{\mathrm{candidate}}[0:160]&X_{\mathrm{candidate}}[160:256]&V=\mathop{\mathrm{Trunc}}\nolimits_{96}(\mathop{\mathrm{SHA256}}\nolimits(E))\\
18&X_{\mathrm{candidate}}[0:192]&X_{\mathrm{candidate}}[192:256]&V=\mathop{\mathrm{Trunc}}\nolimits_{64}(\mathop{\mathrm{SHA256}}\nolimits(E))\\
21&X_{\mathrm{candidate}}[0:224]&X_{\mathrm{candidate}}[224:256]&V=\mathop{\mathrm{Trunc}}\nolimits_{32}(\mathop{\mathrm{SHA256}}\nolimits(E))
\end{array}
```

Concatenation.

```math
D_i = \mathrm{DS\_SALT}\Vert\mathop{\mathrm{BE32}}\nolimits(\mathrm{MEM})\Vert\mathop{\mathrm{BE32}}\nolimits(\mathrm{PIM})\Vert\mathop{\mathrm{BE32}}\nolimits(i)\Vert R,
```

Wide probability: $`\mathop{\mathrm{Pr}}\nolimits [ Y = y , G = g ] = {2}^{- 256} \cdot \mathop{\mathrm{Pr}}\nolimits [ {G}^{\prime} \text{ agrees with } g \text{ outside the first } r \text{ bits at } {e}_{y} ] \cdot 1 [ {\mathrm{Trunc}}_{r} g ( {e}_{y} ) = {v}_{y} ]`$, and this punctuation belongs to the preceding expression.

- A nested probability example.
  - Nested: $`\mathop{\mathrm{Pr}}\nolimits [ Y = y , G = g ] = {2}^{- 256} \cdot \mathop{\mathrm{Pr}}\nolimits [ {G}^{\prime} \text{ agrees with } g \text{ outside the first } r \text{ bits at } {e}_{y} ] \cdot 1 [ {\mathrm{Trunc}}_{r} g ( {e}_{y} ) = {v}_{y} ]`$, followed by text.

Short punctuation: $x$, $y$. Then $z$; and $w$: all four marks remain ordinary text.

Norms: $`\Vert x\Vert + \left\Vert y\right\Vert + \bigl\Vert z\bigr\Vert + \lVert u\rVert`$.

Primed concatenation: $`A'\Vert B\Vert C`$.

```math
\begin{array}{l|c|r}
\text{Left}&\text{Centre}&\text{Right}\\\hline
1&22&333\\
111&2&3
\end{array}
```

```math
\begin{aligned}
a&=b,& c&=d,& e&=f\\
g&=h,& i&=j,& k&=l
\end{aligned}
\tag{A}
```

Inline parts: $`T(x)=\mathop{\mathrm{top}}\nolimits(\lfloor x\rfloor)+(x-\lfloor x\rfloor)\cdot p_{\lfloor x\rfloor+1}`$,
$`\mathop{\mathrm{Pr}}\nolimits [ P\in C ] =\mathop{\mathrm{Exp}}\nolimits [ \sum_{w\in C}\mathop{\mathrm{Pr}}\nolimits [ P=w ] ] \le 2^{-128}+\frac{q_G}{2^{128}}`$,
$`c\ge(1/2-\varepsilon_W-2^{-512})\cdot N_1\cdot(12\cdot C_A+N_2\cdot C_S)-\delta_{\mathrm{gen}}`$ and
$`x=-y+\lvert z+w\rvert\oplus v\land u\to t`$.
