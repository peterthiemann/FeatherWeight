open import FJ.Syntax
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; proj₁; proj₂; _,_)
open import Data.List using (List; map)

module FJ.Lookup (CT : ClassTable) where


fields : Class → Fields
fields Object = ∅
fields (Extend cn D) with declOf cn CT
... | nothing = ∅
... | just (class name fls flds mts mths) = fields D ++ flds

mtype : MethName → Class → Maybe MethType
mtype m Object = nothing
mtype m (Extend cn D) with declOf cn CT
... | nothing = mtype m D
... | just (class name fls flds mts mths) with declOf m mths
... | nothing = mtype m D
... | just record { name = _ ; args = args ; ty = ty ; body = body } = just (args , ty)

mbody : MethName → Class → Maybe MethBody
mbody m Object = nothing
mbody m (Extend cn D) with declOf cn CT
... | nothing = nothing
... | just (class name fls flds mts mths) with declOf m mths
... | nothing = mbody m D
... | just record { name = _ ; args = args ; ty = ty ; body = body } = just (dom args , body)


