unbounded ESS
请在prereq的0.1.5 Extension Spectral Sequence 小节修改，将现在bounded的ESS扩展到unbounded版本；
路线：

假设E1 A1和 E2 A2是converging SS

本节所有的filtration都bounded below

1.	定义truncated 谱序列：对V和所有的E进行截断，给定了s，截断的谱序列为将filtration degree 在大于s之的V都变成0，A改成相应的squotient
2.	E A的所有截断构成一个inverse system
3.	E A 是其所有截断的反向极限
4.	定义extension 谱序列为Ei Ai截断之后的extension谱序列的反向极限，其中pageIso证明如下：
5.	证明对于固定的filtration degree，以及给定的dr，当截断足够大时，extension谱序列的相应部分和截断的谱序列一样
6.	定义A的完备化等于其截断的反向极限
7.	证明，如果A满足mittag-lefter条件，那么ess收敛到Ai的完备化的二项谱序列的同调
