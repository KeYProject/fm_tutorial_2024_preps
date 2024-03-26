#!/bin/sh -xe

CI_TOOL=../tools/key-citool-1.6.0-mini.jar
KEY=../tools/key-2.13.0-exe.jar

java -cp $KEY:$CI_TOOL de.uka.ilkd.key.CheckerKt --proof-path proofs project.key 2>&1 | tee prove.log
