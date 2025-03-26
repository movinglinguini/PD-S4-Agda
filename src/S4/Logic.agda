open import Relation.Binary.Definitions

module S4.Logic 
  (PropAtom : Set) 
  (_≟ₚ_ : DecidableEquality PropAtom)
  where
  {- Repackage components of S4. -}
  open import S4.Core.Hypothesis public
  open import S4.Core.Proposition PropAtom _≟ₚ_ public
  open import S4.Core.Rules PropAtom _≟ₚ_ public

  {- Repackage S4 lemmas -}
  open import S4.Properties PropAtom _≟ₚ_ public
