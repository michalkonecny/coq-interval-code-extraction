{-# OPTIONS_GHC -cpp -XMagicHash #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Main where

import System.Environment

import Logistic_map_s_n

main =
    do
    [sS, nS] <- getArgs
    let s = read sS
    let n = read nS
    let (Approx m e s1) = logistic_map_s_n s n
    print (m,e,s1)
    
