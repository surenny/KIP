Synthetic Nu的修改意见

1.	增加公理：Nu is additive
2.	手动删除nu_commShift
3.	增加定理：nu(shiftFunctor n X) = biShift (n,n) (nu X)，用归纳法证明
4.	完成后面的TODO
5.	AI以为的BHS Axiom 3.1不对，删掉
6.	Nu_lax_monoidal删掉
7.	增加公理：若 X->Y->Z是StebleHomotopoy里面的cofiber sequence，且同调群的序列 0 -> HF2_*X -> HF2_*Y -> HF2_*Z -> 0 为短正合列，则 nu X -> nu Y -> nu Z为distingguished triangle
8.	在cohomology一节中，加上万有系数定理：X的mod 2上同调标准同构于 X的mod 2同调的对偶空间
9.	叙述上述 7 的上同调版本
10.	公理7的另一方向的等价性暂时删除不要
