# 由于unboundedESS形式化得并不顺利，此文件存放加细但是还没有放入系统的hint：

对于/inspire/hdd/project/qproject-fundationmodel/czxs25250150/Archon/workspace/ESS-conv/ESSConv/SpectralSequence/UnboundedExtension.lean 里的四个sorry，前3个sorry见/inspire/hdd/project/qproject-fundationmodel/czxs25250150/KIP/docs/unboundedness.tex

最后一个sorry：

unbounded ESS

假设E1 A1和 E2 A2是converging SS

本节所有的filtration都bounded below

1.	定义truncated 谱序列：对V和所有的E进行截断，给定了s，截断的谱序列为将filtration degree 在大于s之的V都变成0，A改成相应的squotient
2.	E A的所有截断构成一个inverse system
3.	E  是其所有截断的反向极限
4.	如果A完备，则 E A的所有截断的反向极限为 E A
5.	定义extension 谱序列为Ei Ai截断之后的extension谱序列的在（不要converging）谱序列范畴中的反向极限，其中pageIso证明如下：
6.	证明对于固定的filtration degree，以及给定的dr，当截断足够大时，extension谱序列的相应部分和截断的谱序列一样
7.	定义A的完备化等于其截断的反向极限
8.	证明，如果A的同调满足mittag-lefter条件，那么ess收敛到Ai的完备化的二项谱序列的同调
9.	8的证明，cokernel部分：cokernel的filtration由A2的filtration的像诱导，graded piece为：FsA2/（F{s+1}A2+Im（d）），因为filtration bounded below，当k足够小时，这个等于 FsA2/（F{s+1}+Im（dr：FkA2->A2）））
10.	8的证明，kernel部分：kernel的filtration由A1的filtration限制，graded piece为FsA1∩ker（d）/F{s+1}。
11.	另一方面，由ML条件，ker（dr）当r足够大时，不依赖于r。这时ker（dr）包含于任意的FsA2，根据A2的完备性假设（其实只要separated），这等于d的kernel。
12.	也就是说kernel的graded piece等于FsA1∩ker（dr）/F{s+1}，当r足够大。
13.	然后利用Er与truncated Er的同构证明8
