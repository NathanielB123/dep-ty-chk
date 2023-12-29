open import DepTyChk.Abstract using (Syntax)
import DepTyChk.Concrete as Concrete

module DepTyChk.Instantiated where

cubicalSyntax : Syntax
cubicalSyntax = record { Concrete }
