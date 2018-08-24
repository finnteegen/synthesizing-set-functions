#!/bin/sh

# Testing all example programs with CurryCheck

CURRDIR=`pwd`
CURRYCHECK="curry-check"

cd $CURRDIR/Simple        && $CURRYCHECK Anyof NDConst Queens
cd $CURRDIR/Sharing       && $CURRYCHECK Anyof NDConst Queens Sharing
cd $CURRDIR/Nested        && $CURRYCHECK Anyof NDConst Nested Not Queens
cd $CURRDIR/NestedSharing && $CURRYCHECK Anyof HigherOrder Nested NestedSharing Not Queens Sharing
