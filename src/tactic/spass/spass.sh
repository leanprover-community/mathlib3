#!/bin/sh

echo $1 > $2

SPASS -TPTP -PGiven=0 -PProblem=0 -Splits=0 -DocProof $2
