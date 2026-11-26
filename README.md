# 图 17 的无限棋盘：三种取法下，两堆石子的全部必败位置

**BI1XLN 和 GPT-6.2 Astra** · 2026 年 11 月 26 日

[中文证明 PDF（含图解）](Figure17-proof-zh.pdf) · [Lean 4 证明源码](Figure17.lean)

两人轮流从两堆石子中取走 $(1,2)$、$(3,4)$ 或 $(4,6)$。两堆都要够取，无合法走法的一方输。Urban Larsson、Indrajit Saha 和 Makoto Yokoo 在 2024 年论文的图 17 中给出了这个游戏的着色规则，并提出验证中间区域的问题。[原论文](https://doi.org/10.1016/j.tcs.2024.114775) · [作者预印本，第 24–25 页](https://arxiv.org/pdf/2307.12458v4#page=24)

## 如何判断任意位置的胜负

两堆分别有 $x,y$ 颗石子。令 $h=\lfloor y/2\rfloor$、$A=3h-2x$、$B=6x-7h$。找到下表对应的一行，条件成立时，轮到走棋的一方必败。

| 区域 | 必败的充要条件 |
| --- | --- |
| $A<0$ | $h\bmod 4=0$ |
| $B<0$ | $x\bmod 7$ 为 $0$ 或 $2$ |
| $A\ge 0$ 且 $B\ge 0$ | $B\bmod 8$ 为 $0$ 或 $6$ |

例如 $(7,12)$ 给出 $h=6$、$A=4$、$B=0$，所以先手必败。从 $(8,14)$ 可以取走 $(1,2)$，将这个必败位置留给对手。

## 验证证明

在仓库目录中使用 Lean 4.36.0 运行以下命令。源码只依赖 Lean 自带的标准库。

```sh
lean -DwarningAsError=true Figure17.lean
```

`Figure17.original_middle` 验证原图中间区域的递归着色，`Figure17.original_quickTest` 证明上表适用于所有非负整数坐标。`Figure17.scaled_figure17` 把结论推广到三种取法同时放大相同的正整数倍。PDF 另给出了生成函数证明，`Figure17.generating_identity` 核验其中用到的多项式恒等式。
