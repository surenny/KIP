Synthitic basic修改意见

1.	重写lambda^n 的部分：首先用归纳定义 lambda^n，然后仿照X/lambda的操作，利用lambda^n来定义X/lambda^n，并定义相应的distinguidhed triangle
2.	XmodLambda.triangle_distinguished 和 xModLambda_cofiberSeq重复，进行合并
3.	xModLambdaN_cofiberSeq 删除
4.	证明zlambda_enrichment ：首先用可加性推出enriched over Z，然后用lambda的定义证明hom上面有lambda运算（证明两种方式定义的lambda运算相同），最后利用Z[lambda]的万有性质构造模结构
