open import Relation.Binary.Definitions

module S4.Logic 
  (PropAtom : Set) 
  (_≟ₐ_ : DecidableEquality PropAtom)
  where
  {- Repackage components of S4. -}
  open import S4.Core.Hypothesis hiding (_∙_⇒_) renaming (_≟_ to _≟ₕ_) public 
  open import S4.Core.Proposition PropAtom _≟ₐ_ renaming (_≟_ to _≟ₚ_) public
  open import S4.Core.Context PropAtom _≟ₐ_ public
  open import S4.Core.Rules PropAtom _≟ₐ_ public

  {- Repackage S4 lemmas -}
  open import S4.Properties PropAtom _≟ₐ_ public
