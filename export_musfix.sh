#!/bin/bash

search_dir="tests/**/*.fq"

stack build && 
for file in ${search_dir}; do
	stack exec -- fixpoint ${file}
	extensionless=${file%.fq}
	filename=${extensionless#*/} 
	mv lqfp2musfix.smt2 ../musfix/test/${filename}.smt2_
done
