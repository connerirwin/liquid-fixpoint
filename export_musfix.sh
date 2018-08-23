#!/bin/bash

for file in "$@"; do
	stack exec -- fixpoint ${file}
	filename=$(basename ${file} .fq)
	mv lqfp2musfix.smt2 ../musfix/test/liquid/${filename}.smt2 
done
