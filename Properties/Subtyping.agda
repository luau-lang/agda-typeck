{-# OPTIONS --rewriting #-}

module Properties.Subtyping where

open import Agda.Builtin.Equality using (_≡_; refl)
open import FFI.Data.Either using (Either; Left; Right; mapLR; swapLR; cond)
open import FFI.Data.Maybe using (Maybe; just; nothing)
open import Luau.Subtyping using (_<:_; _≮:_; LValue; Language; ¬Language; Language!; ¬Language!; witness; unknown; never; scalar; function; scalar-function; scalar-scalar; scalar-error; function-scalar; function-ok; function-ok₁; function-ok₀; function-error; function-error₀; function-error₁; function-nok; function-diverge; left; right; _,_; _↦_; ⟨⟩; ⟨_⟩; error; diverge)
open import Luau.Type using (Type; Scalar; nil; number; string; boolean; error; never; unknown; _⇒_; _∪_; _∩_; skalar; funktion; any)
open import Properties.Contradiction using (CONTRADICTION; ¬; ⊥)
open import Properties.Equality using (_≢_)
open import Properties.Functions using (_∘_)
open import Properties.Product using (_×_; _,_)

-- Language membership is decidable
dec-language : ∀ T t → Either (¬Language T t) (Language T t)
dec-language nil ⟨ scalar number ⟩ = Left (scalar-scalar number nil (λ ()))
dec-language nil ⟨ scalar boolean ⟩ = Left (scalar-scalar boolean nil (λ ()))
dec-language nil ⟨ scalar string ⟩ = Left (scalar-scalar string nil (λ ()))
dec-language nil ⟨ scalar nil ⟩ = Right (scalar nil)
dec-language nil ⟨ s ↦ t ⟩ = Left (scalar-function nil)
dec-language boolean ⟨ scalar number ⟩ = Left (scalar-scalar number boolean (λ ()))
dec-language boolean ⟨ scalar boolean ⟩ = Right (scalar boolean)
dec-language boolean ⟨ scalar string ⟩ = Left (scalar-scalar string boolean (λ ()))
dec-language boolean ⟨ scalar nil ⟩ = Left (scalar-scalar nil boolean (λ ()))
dec-language boolean ⟨ s ↦ t ⟩ = Left (scalar-function boolean)
dec-language number ⟨ scalar number ⟩ = Right (scalar number)
dec-language number ⟨ scalar boolean ⟩ = Left (scalar-scalar boolean number (λ ()))
dec-language number ⟨ scalar string ⟩ = Left (scalar-scalar string number (λ ()))
dec-language number ⟨ scalar nil ⟩ = Left (scalar-scalar nil number (λ ()))
dec-language number ⟨ s ↦ t ⟩ = Left (scalar-function number)
dec-language string ⟨ scalar number ⟩ = Left (scalar-scalar number string (λ ()))
dec-language string ⟨ scalar boolean ⟩ = Left (scalar-scalar boolean string (λ ()))
dec-language string ⟨ scalar string ⟩ = Right (scalar string)
dec-language string ⟨ scalar nil ⟩ = Left (scalar-scalar nil string (λ ()))
dec-language string ⟨ s ↦ t ⟩ = Left (scalar-function string)
dec-language (T₁ ⇒ T₂) ⟨ scalar s ⟩ = Left (function-scalar s)
dec-language (T₁ ⇒ T₂) ⟨ ⟨ s ⟩ ↦ ⟨ t ⟩ ⟩ = cond (Right ∘ function-nok) (λ p → mapLR (function-ok₁ p) function-ok (dec-language T₂ ⟨ t ⟩)) (dec-language T₁ ⟨ s ⟩)
dec-language (T₁ ⇒ T₂) ⟨ ⟨ s ⟩ ↦ diverge ⟩ = cond (Right ∘ function-nok) (λ _ → Right function-diverge) (dec-language T₁ ⟨ s ⟩)
dec-language (T₁ ⇒ T₂) ⟨ ⟨ s ⟩ ↦ error ⟩ = cond (Right ∘ function-nok) (λ p → mapLR (function-error₁ p) function-error (dec-language T₂ error)) (dec-language T₁ ⟨ s ⟩)
dec-language (T₁ ⇒ T₂) ⟨ ⟨⟩ ↦ error ⟩ = mapLR function-error₀ function-error (dec-language T₂ error)
dec-language (T₁ ⇒ T₂) ⟨ ⟨⟩ ↦ diverge ⟩ = Right function-diverge
dec-language (T₁ ⇒ T₂) ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩ = mapLR function-ok₀ function-ok (dec-language T₂ ⟨ t ⟩)
dec-language never t = Left never
dec-language unknown t = Right unknown
dec-language (T₁ ∪ T₂) t = cond (λ p → cond (Left ∘ _,_ p) (Right ∘ right) (dec-language T₂ t)) (Right ∘ left) (dec-language T₁ t)
dec-language (T₁ ∩ T₂) t = cond (Left ∘ left) (λ p → cond (Left ∘ right) (Right ∘ _,_ p) (dec-language T₂ t)) (dec-language T₁ t)
dec-language nil error = Left (scalar-error nil)
dec-language (T ⇒ T₁) error = Left function-error
dec-language boolean error = Left (scalar-error boolean)
dec-language number error = Left (scalar-error number)
dec-language string error = Left (scalar-error string)
dec-language error error = Right error
dec-language error ⟨ t ⟩ = Left error

-- ¬Language T is the complement of Language T
language-comp : ∀ {T t} → ¬Language T t → ¬(Language T t)
language-comp (p₁ , p₂) (left q) = language-comp p₁ q
language-comp (p₁ , p₂) (right q) = language-comp p₂ q
language-comp (left p) (q₁ , q₂) = language-comp p q₁
language-comp (right p) (q₁ , q₂) = language-comp p q₂
language-comp (scalar-scalar s p₁ p₂) (scalar s) = p₂ refl
language-comp never (scalar ())
language-comp (scalar-function ()) (function-ok p)
language-comp (scalar-error ()) error
language-comp (function-ok₀ p) (function-ok q) = language-comp p q
language-comp (function-ok₁ p₁ p₂) (function-nok q) = language-comp q p₁
language-comp (function-ok₁ p₁ p₂) (function-ok q) = language-comp p₂ q
language-comp (function-error₀ p) (function-error q) = language-comp p q
language-comp (function-error₁ p₁ p₂) (function-nok q) = language-comp q p₁
language-comp (function-error₁ p₁ p₂) (function-error q) = language-comp p₂ q
language-comp error (scalar ())

-- ≮: is the complement of <:
¬≮:-impl-<: : ∀ {T U} → ¬(T ≮: U) → (T <: U)
¬≮:-impl-<: {T} {U} p {t} q with dec-language U t
¬≮:-impl-<: {T} {U} p q | Left r = CONTRADICTION (p (witness q r))
¬≮:-impl-<: {T} {U} p q | Right r = r

<:-impl-¬≮: : ∀ {T U} → (T <: U) → ¬(T ≮: U)
<:-impl-¬≮: p (witness q r) = language-comp r (p q)

<:-impl-⊇ : ∀ {T U} → (T <: U) → ∀ {t} → ¬Language U t → ¬Language T t
<:-impl-⊇ {T} p {t} q with dec-language T t
<:-impl-⊇ p q | Left r = r
<:-impl-⊇ p q | Right r = CONTRADICTION (language-comp q (p r))

-- reflexivity
≮:-refl : ∀ {T} → ¬(T ≮: T)
≮:-refl (witness p q) = language-comp q p

<:-refl : ∀ {T} → (T <: T)
<:-refl = ¬≮:-impl-<: ≮:-refl

-- transititivity
≮:-trans-≡ : ∀ {S T U} → (S ≮: T) → (T ≡ U) → (S ≮: U)
≮:-trans-≡ p refl = p

<:-trans-≡ : ∀ {S T U} → (S <: T) → (T ≡ U) → (S <: U)
<:-trans-≡ p refl = p

≡-impl-<: : ∀ {T U} → (T ≡ U) → (T <: U)
≡-impl-<: refl = <:-refl

≡-trans-≮: : ∀ {S T U} → (S ≡ T) → (T ≮: U) → (S ≮: U)
≡-trans-≮: refl p = p

≡-trans-<: : ∀ {S T U} → (S ≡ T) → (T <: U) → (S <: U)
≡-trans-<: refl p = p

≮:-trans : ∀ {S T U} → (S ≮: U) → Either (S ≮: T) (T ≮: U)
≮:-trans {T = T} (witness p q) = mapLR (witness p) (λ z → witness z q) (dec-language T _)

<:-trans : ∀ {S T U} → (S <: T) → (T <: U) → (S <: U)
<:-trans p q r = q (p r)

<:-trans-≮: : ∀ {S T U} → (S <: T) → (S ≮: U) → (T ≮: U)
<:-trans-≮: p (witness q r) = witness (p q) r

≮:-trans-<: : ∀ {S T U} → (S ≮: U) → (T <: U) → (S ≮: T)
≮:-trans-<: (witness p q) r = witness p (<:-impl-⊇ r q)

-- Properties of union

<:-union : ∀ {R S T U} → (R <: T) → (S <: U) → ((R ∪ S) <: (T ∪ U))
<:-union p q (left r) = left (p r)
<:-union p q (right r) = right (q r)

<:-∪-left : ∀ {S T} → S <: (S ∪ T)
<:-∪-left p = left p

<:-∪-right : ∀ {S T} → T <: (S ∪ T)
<:-∪-right p = right p

<:-∪-lub : ∀ {S T U} → (S <: U) → (T <: U) → ((S ∪ T) <: U)
<:-∪-lub p q (left r) = p r
<:-∪-lub p q (right r) = q r

<:-∪-symm : ∀ {T U} → (T ∪ U) <: (U ∪ T)
<:-∪-symm (left p) = right p
<:-∪-symm (right p) = left p

<:-∪-assocl : ∀ {S T U} → (S ∪ (T ∪ U)) <: ((S ∪ T) ∪ U)
<:-∪-assocl (left p) = left (left p)
<:-∪-assocl (right (left p)) = left (right p)
<:-∪-assocl (right (right p)) = right p

<:-∪-assocr : ∀ {S T U} → ((S ∪ T) ∪ U) <: (S ∪ (T ∪ U))
<:-∪-assocr (left (left p)) = left p
<:-∪-assocr (left (right p)) = right (left p)
<:-∪-assocr (right p) = right (right p)

≮:-∪-left : ∀ {S T U} → (S ≮: U) → ((S ∪ T) ≮: U)
≮:-∪-left (witness p q) = witness (left p) q

≮:-∪-right : ∀ {S T U} → (T ≮: U) → ((S ∪ T) ≮: U)
≮:-∪-right (witness p q) = witness (right p) q

≮:-left-∪ : ∀ {S T U} → (S ≮: (T ∪ U)) → (S ≮: T)
≮:-left-∪ (witness p (q₁ , q₂)) = witness p q₁

≮:-right-∪ : ∀ {S T U} → (S ≮: (T ∪ U)) → (S ≮: U)
≮:-right-∪ (witness p (q₁ , q₂)) = witness p q₂

-- Properties of intersection

<:-intersect : ∀ {R S T U} → (R <: T) → (S <: U) → ((R ∩ S) <: (T ∩ U))
<:-intersect p q (r₁ , r₂) = (p r₁ , q r₂)

<:-∩-left : ∀ {S T} → (S ∩ T) <: S
<:-∩-left (p , _) = p

<:-∩-right : ∀ {S T} → (S ∩ T) <: T
<:-∩-right (_ , p) = p

<:-∩-glb : ∀ {S T U} → (S <: T) → (S <: U) → (S <: (T ∩ U))
<:-∩-glb p q r = (p r , q r)

<:-∩-symm : ∀ {T U} → (T ∩ U) <: (U ∩ T)
<:-∩-symm (p₁ , p₂) = (p₂ , p₁)

<:-∩-assocl : ∀ {S T U} → (S ∩ (T ∩ U)) <: ((S ∩ T) ∩ U)
<:-∩-assocl (p , (p₁ , p₂)) = (p , p₁) , p₂

<:-∩-assocr : ∀ {S T U} → ((S ∩ T) ∩ U) <: (S ∩ (T ∩ U))
<:-∩-assocr ((p , p₁) , p₂) = p , (p₁ , p₂)

≮:-∩-left : ∀ {S T U} → (S ≮: T) → (S ≮: (T ∩ U))
≮:-∩-left (witness p q) = witness p (left q)

≮:-∩-right : ∀ {S T U} → (S ≮: U) → (S ≮: (T ∩ U))
≮:-∩-right (witness p q) = witness p (right q)

-- Distribution properties
<:-∩-distl-∪ : ∀ {S T U} → (S ∩ (T ∪ U)) <: ((S ∩ T) ∪ (S ∩ U))
<:-∩-distl-∪ (p₁ , left p₂) = left (p₁ , p₂)
<:-∩-distl-∪ (p₁ , right p₂) = right (p₁ , p₂)

∩-distl-∪-<: : ∀ {S T U} → ((S ∩ T) ∪ (S ∩ U)) <: (S ∩ (T ∪ U))
∩-distl-∪-<: (left (p₁ , p₂)) = (p₁ , left p₂)
∩-distl-∪-<: (right (p₁ , p₂)) = (p₁ , right p₂)

<:-∩-distr-∪ : ∀ {S T U} → ((S ∪ T) ∩ U) <:  ((S ∩ U) ∪ (T ∩ U))
<:-∩-distr-∪ (left p₁ , p₂) = left (p₁ , p₂)
<:-∩-distr-∪ (right p₁ , p₂) = right (p₁ , p₂)

∩-distr-∪-<: : ∀ {S T U} → ((S ∩ U) ∪ (T ∩ U)) <: ((S ∪ T) ∩ U)
∩-distr-∪-<: (left (p₁ , p₂)) = (left p₁ , p₂)
∩-distr-∪-<: (right (p₁ , p₂)) = (right p₁ , p₂)

<:-∪-distl-∩ : ∀ {S T U} → (S ∪ (T ∩ U)) <: ((S ∪ T) ∩ (S ∪ U))
<:-∪-distl-∩ (left p) = (left p , left p)
<:-∪-distl-∩ (right (p₁ , p₂)) = (right p₁ , right p₂)

∪-distl-∩-<: : ∀ {S T U} → ((S ∪ T) ∩ (S ∪ U)) <: (S ∪ (T ∩ U))
∪-distl-∩-<: (left p₁ , p₂) = left p₁
∪-distl-∩-<: (right p₁ , left p₂) = left p₂
∪-distl-∩-<: (right p₁ , right p₂) = right (p₁ , p₂)

<:-∪-distr-∩ : ∀ {S T U} → ((S ∩ T) ∪ U) <: ((S ∪ U) ∩ (T ∪ U))
<:-∪-distr-∩ (left (p₁ , p₂)) = left p₁ , left p₂
<:-∪-distr-∩ (right p) = (right p , right p)

∪-distr-∩-<: : ∀ {S T U} → ((S ∪ U) ∩ (T ∪ U)) <: ((S ∩ T) ∪ U)
∪-distr-∩-<: (left p₁ , left p₂) = left (p₁ , p₂)
∪-distr-∩-<: (left p₁ , right p₂) = right p₂
∪-distr-∩-<: (right p₁ , p₂) = right p₁

∩-<:-∪ : ∀ {S T} → (S ∩ T) <: (S ∪ T)
∩-<:-∪ (p , _) = left p

-- Properties of functions
<:-function : ∀ {R S T U} → (R <: S) → (T <: U) → (S ⇒ T) <: (R ⇒ U)
<:-function p q (function-ok r) = function-ok (q r)
<:-function p q (function-nok r) = function-nok (<:-impl-⊇ p r)
<:-function p q (function-error r) = function-error (q r)
<:-function p q function-diverge = function-diverge

<:-function-∩-∩ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∩ S) ⇒ (T ∩ U))
<:-function-∩-∩ (function-ok p , function-ok q) = function-ok (p , q)
<:-function-∩-∩ (function-nok p , q) = function-nok (left p)
<:-function-∩-∩ (p , function-nok q) = function-nok (right q)
<:-function-∩-∩ (function-error p , function-error q) = function-error (p , q)
<:-function-∩-∩ (function-diverge , q) = function-diverge

<:-function-∩-∪ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∪ S) ⇒ (T ∪ U))
<:-function-∩-∪ (function-ok p , q) = function-ok (left p)
<:-function-∩-∪ (function-error p , q) = function-error (left p)
<:-function-∩-∪ (function-diverge , q) = function-diverge
<:-function-∩-∪ (function-nok p , function-nok q) = function-nok (p , q)
<:-function-∩-∪ (p , function-ok q) = function-ok (right q)
<:-function-∩-∪ (p , function-error q) = function-error (right q)
<:-function-∩-∪ (p , function-diverge) = function-diverge

<:-function-∩ : ∀ {S T U} → ((S ⇒ T) ∩ (S ⇒ U)) <: (S ⇒ (T ∩ U))
<:-function-∩ (function-nok p , q) = function-nok p
<:-function-∩ (function-diverge , q) = function-diverge
<:-function-∩ (p , function-nok x) = function-nok x
<:-function-∩ (function-ok p , function-ok q) = function-ok (p , q)
<:-function-∩ (function-error p , function-error q) = function-error (p , q)

<:-function-∪ : ∀ {R S T U} → ((R ⇒ S) ∪ (T ⇒ U)) <: ((R ∩ T) ⇒ (S ∪ U))
<:-function-∪ (left (function-ok p)) = function-ok (left p)
<:-function-∪ (left (scalar ()))
<:-function-∪ (left (function-nok p)) = function-nok (left p)
<:-function-∪ (left (function-error p)) = function-error (left p)
<:-function-∪ (left function-diverge) = function-diverge
<:-function-∪ (right (function-ok p)) = function-ok (right p)
<:-function-∪ (right (function-nok p)) = function-nok (right p)
<:-function-∪ (right (function-error p)) = function-error (right p)
<:-function-∪ (right function-diverge) = function-diverge

<:-function-∪-∩ : ∀ {R S T U} → ((R ∩ S) ⇒ (T ∪ U)) <: ((R ⇒ T) ∪ (S ⇒ U))
<:-function-∪-∩ (function-ok (left p)) = left (function-ok p)
<:-function-∪-∩ (function-ok (right p)) = right (function-ok p)
<:-function-∪-∩ (function-nok (left p)) = left (function-nok p)
<:-function-∪-∩ (function-nok (right p)) = right (function-nok p)
<:-function-∪-∩ (function-error (left p)) = left (function-error p)
<:-function-∪-∩ (function-error (right p)) = right (function-error p)
<:-function-∪-∩ function-diverge = left function-diverge

-- <:-function-left : ∀ {R S T U} → (any ≮: U) → (S ⇒ T) <: (R ⇒ U) → (R <: S)
-- <:-function-left {R} {S} (witness _ ¬Uu) p {⟨ s ⟩} Rs with dec-language S ⟨ s ⟩
-- <:-function-left (witness _ ¬Uu) p Rs | Right Ss = Ss
-- <:-function-left (witness {⟨ u ⟩} _ ¬Uu) p Rs | Left ¬Ss with p (function-nok {u = ⟨ u ⟩} ¬Ss)
-- <:-function-left (witness _ ¬Uu) p {⟨ _ ⟩} Rs | Left ¬Ss | function-nok ¬Rs = CONTRADICTION (language-comp ¬Rs Rs)
-- <:-function-left (witness _ ¬Uu) p {⟨ _ ⟩} Rs | Left ¬Ss | function-ok Uu = CONTRADICTION (language-comp ¬Uu Uu)
-- <:-function-left (witness {error} _ ¬Uu) p Rs | Left ¬Ss with p (function-nok {u = error} ¬Ss)
-- <:-function-left (witness _ ¬Uu) p {⟨ _ ⟩} Rs | Left ¬Ss | function-nok ¬Rs = CONTRADICTION (language-comp ¬Rs Rs)
-- <:-function-left (witness _ ¬Uu) p {⟨ _ ⟩} Rs | Left ¬Ss | function-error Uu = CONTRADICTION (language-comp ¬Uu Uu)
-- <:-function-left {R} {S} (witness _ ¬Uu) p {error} Rs with dec-language S error
-- <:-function-left {R} {S} (witness _ ¬Uu) p {error} Rs | Right Ss = Ss
-- <:-function-left {R} {S} (witness _ ¬Uu) p {error} Rs | Left ¬Ss = {!!}

<:-function-right : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (T <: U)
<:-function-right p {⟨ t ⟩} Tt with p (function-ok {t = ⟨⟩} Tt)
<:-function-right p {⟨ t ⟩} Tt | function-ok Ut = Ut
<:-function-right p {error} Tt with p (function-error {t = ⟨⟩} Tt)
<:-function-right p {error} Tt | function-error Ut = Ut

≮:-function-left : ∀ {R S T U} → (R ≮: S) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-left (witness p q) = {!!} -- witness (function-ok q) ? -- (function-err₁ p)

≮:-function-right : ∀ {R S T U} → (T ≮: U) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-right (witness p q) = {!!} -- witness (function-ok₂ p) (function-tgt q)

-- Properties of scalars
skalar-function-ok : ∀ {s t} → (¬Language skalar ⟨ s ↦ t ⟩)
skalar-function-ok = scalar-function number ,
                       (scalar-function string ,
                        (scalar-function nil , scalar-function boolean)) -- (scalar-function-ok number , (scalar-function-ok string , (scalar-function-ok nil , scalar-function-ok boolean)))

scalar-<: : ∀ {S T} → (s : Scalar S) → Language T ⟨ scalar s ⟩ → (S <: T)
scalar-<: number p (scalar number) = p
scalar-<: boolean p (scalar boolean) = p
scalar-<: string p (scalar string) = p
scalar-<: nil p (scalar nil) = p

scalar-∩-function-<:-never : ∀ {S T U} → (Scalar S) → ((T ⇒ U) ∩ S) <: never
scalar-∩-function-<:-never number (() , scalar number)
scalar-∩-function-<:-never boolean (() , scalar boolean)
scalar-∩-function-<:-never string (() , scalar string)
scalar-∩-function-<:-never nil (() , scalar nil)

function-≮:-scalar : ∀ {S T U} → (Scalar U) → ((S ⇒ T) ≮: U)
function-≮:-scalar s = witness function-diverge (scalar-function s) -- witness (function-ok₂ {!!}) (scalar-function-ok s) -- witness (⟨⟩ ↦ diverge) ? ? -- function-diverge (scalar-function-ok s)

scalar-≮:-function : ∀ {S T U} → (Scalar U) → (U ≮: (S ⇒ T))
scalar-≮:-function s = witness (scalar s) (function-scalar s)

unknown-≮:-scalar : ∀ {U} → (Scalar U) → (unknown ≮: U)
unknown-≮:-scalar s = witness unknown {!!} -- (scalar-function-ok s)

scalar-≮:-never : ∀ {U} → (Scalar U) → (U ≮: never)
scalar-≮:-never s = witness (scalar s) never

scalar-≢-impl-≮: : ∀ {T U} → (Scalar T) → (Scalar U) → (T ≢ U) → (T ≮: U)
scalar-≢-impl-≮: s₁ s₂ p = witness (scalar s₁) (scalar-scalar s₁ s₂ p)

scalar-≢-∩-<:-never : ∀ {T U V} → (Scalar T) → (Scalar U) → (T ≢ U) → (T ∩ U) <: V
scalar-≢-∩-<:-never s t p (scalar s₁ , scalar s₂) = CONTRADICTION (p refl)

skalar-scalar : ∀ {T} (s : Scalar T) → (Language skalar ⟨ scalar s ⟩)
skalar-scalar number = left (scalar number)
skalar-scalar boolean = right (right (right (scalar boolean)))
skalar-scalar string = right (left (scalar string))
skalar-scalar nil = right (right (left (scalar nil)))

-- Properties of unknown and never
unknown-≮: : ∀ {T U} → (T ≮: U) → (unknown ≮: U)
unknown-≮: (witness p q) = witness unknown q

never-≮: : ∀ {T U} → (T ≮: U) → (T ≮: never)
never-≮: (witness p q) = witness p never

unknown-≮:-never : (unknown ≮: never)
unknown-≮:-never = witness {t = ⟨ scalar nil ⟩} unknown never

unknown-≮:-function : ∀ {S T} → (unknown ≮: (S ⇒ T))
unknown-≮:-function = witness unknown (function-scalar nil)

function-≮:-never : ∀ {T U} → ((T ⇒ U) ≮: never)
function-≮:-never = witness function-diverge never -- function-diverge never

<:-never : ∀ {T} → (never <: T)
<:-never (scalar ())

≮:-never-left : ∀ {S T U} → (S <: (T ∪ U)) → (S ≮: T) → (S ∩ U) ≮: never
≮:-never-left p (witness q₁ q₂) with p q₁
≮:-never-left p (witness q₁ q₂) | left r = CONTRADICTION (language-comp q₂ r)
≮:-never-left p (witness q₁ q₂) | right r = witness (q₁ , r) never

≮:-never-right : ∀ {S T U} → (S <: (T ∪ U)) → (S ≮: U) → (S ∩ T) ≮: never
≮:-never-right p (witness q₁ q₂) with p q₁
≮:-never-right p (witness q₁ q₂) | left r = witness (q₁ , r) never
≮:-never-right p (witness q₁ q₂) | right r = CONTRADICTION (language-comp q₂ r)

<:-unknown : ∀ {T} → (T <: unknown)
<:-unknown p = unknown

<:-everything : unknown <: (funktion ∪ skalar)
<:-everything = {!!}
-- <:-everything (scalar s) p = right (skalar-scalar s)
-- <:-everything (s ↦ t) p = left ? -- function

-- A Gentle Introduction To Semantic Subtyping (https://www.cduce.org/papers/gentle.pdf)
-- defines a "set-theoretic" model (sec 2.5)
-- Unfortunately we don't quite have this property, due to uninhabited types,
-- for example (never -> T) is equivalent to (never -> U)
-- when types are interpreted as sets of syntactic values.

_⊆_ : ∀ {A : Set} → (A → Set) → (A → Set) → Set
(P ⊆ Q) = ∀ a → (P a) → (Q a)

_⊗_ : ∀ {A B : Set} → (A → Set) → (B → Set) → ((A × B) → Set)
(P ⊗ Q) (a , b) = (P a) × (Q b)

Comp : ∀ {A : Set} → (A → Set) → (A → Set)
Comp P a = ¬(P a)

Lift : ∀ {A : Set} → (A → Set) → (Maybe A → Set)
Lift P nothing = ⊥
Lift P (just a) = P a

set-theoretic-if : ∀ {S₁ T₁ S₂ T₂} →

  -- This is the "if" part of being a set-theoretic model
  -- though it uses the definition from Frisch's thesis
  -- rather than from the Gentle Introduction. The difference
  -- being the presence of Lift, (written D_Ω in Defn 4.2 of
  -- https://www.cduce.org/papers/frisch_phd.pdf).
  (Language (S₁ ⇒ T₁) ⊆ Language (S₂ ⇒ T₂)) →
  (∀ Q → Q ⊆ Comp((Language S₁) ⊗ Comp(Lift(Language T₁))) → Q ⊆ Comp((Language S₂) ⊗ Comp(Lift(Language T₂))))

set-theoretic-if {S₁} {T₁} {S₂} {T₂} p Q q (t , just u) Qtu (S₂t , ¬T₂u) = q (t , just u) Qtu (S₁t , ¬T₁u) where

  S₁t : Language S₁ t
  S₁t = {!!}
  -- S₁t with dec-language S₁ t
  -- S₁t | Left ¬S₁t with p (function-ok ¬S₁t)
  -- S₁t | Left ¬S₁t | function-ok ¬S₂t = CONTRADICTION (language-comp t ¬S₂t S₂t)
  -- S₁t | Right r = r

  ¬T₁u : ¬(Language T₁ u)
  ¬T₁u = {!!}
  -- ¬T₁u T₁u with p (⟨ t ⟩ ↦ ⟨ u ⟩) (function-ok₂ T₁u)
  -- ¬T₁u T₁u | function-ok ¬S₂t = language-comp t ¬S₂t S₂t
  -- ¬T₁u T₁u | function-ok₂ T₂u = ¬T₂u T₂u

set-theoretic-if {S₁} {T₁} {S₂} {T₂} p Q q (t , nothing) Qt- (S₂t , _) = q (t , nothing) Qt- (S₁t , λ ()) where

  S₁t : Language S₁ t
  S₁t = {!!}
  -- S₁t with dec-language S₁ t
  -- S₁t | Left ¬S₁t with p (⟨ t ⟩ ↦ error) (function-ok ¬S₁t)
  -- S₁t | Left ¬S₁t | function-ok ¬S₂t = CONTRADICTION (language-comp t ¬S₂t S₂t)
  -- S₁t | Right r = r

not-quite-set-theoretic-only-if : ∀ {S₁ T₁ S₂ T₂} →

  -- We don't quite have that this is a set-theoretic model
  -- it's only true when Language S₂ is inhabited
  -- in particular it's not true when S₂ is never,
  ∀ s₂ → Language S₂ s₂ →

  -- This is the "only if" part of being a set-theoretic model
  (∀ Q → Q ⊆ Comp((Language S₁) ⊗ Comp(Lift(Language T₁))) → Q ⊆ Comp((Language S₂) ⊗ Comp(Lift(Language T₂)))) →
  (Language (S₁ ⇒ T₁) ⊆ Language (S₂ ⇒ T₂))

not-quite-set-theoretic-only-if {S₁} {T₁} {S₂} {T₂} s₂ S₂s₂ p = r where

  Q : (LValue × Maybe LValue) → Set
  Q = {!!}
  -- Q (t , just u) = Either (¬Language S₁ t) (Language T₁ u)
  -- Q (t , nothing) = ¬Language S₁ t
  
  q : Q ⊆ Comp(Language S₁ ⊗ Comp(Lift(Language T₁)))
  q = {!!}
  -- q (t , just u) (Left ¬S₁t) (S₁t , ¬T₁u) = language-comp t ¬S₁t S₁t
  -- q (t , just u) (Right T₂u) (S₁t , ¬T₁u) = ¬T₁u T₂u
  -- q (t , nothing) ¬S₁t (S₁t , _) = language-comp t ¬S₁t S₁t
  
  r : Language (S₁ ⇒ T₁) ⊆ Language (S₂ ⇒ T₂)
  r = {!!}
  -- r (⟨ s ⟩ ↦ t) (function-ok ¬S₁s) with dec-language S₂ s
  -- r (⟨ s ⟩ ↦ t) (function-ok ¬S₁s) | Left ¬S₂s = function-ok ¬S₂s
  -- r (⟨ s ⟩ ↦ t) (function-ok ¬S₁s) | Right S₂s = CONTRADICTION (p Q q (s , nothing) ¬S₁s (S₂s , λ ()))
  -- r (s ↦ ⟨ t ⟩) (function-ok₂ T₁t) with dec-language T₂ t
  -- r (⟨ s ⟩ ↦ ⟨ t ⟩) (function-ok₂ T₁t) | Left ¬T₂t with dec-language S₂ s
  -- r (⟨ s ⟩ ↦ ⟨ t ⟩) (function-ok₂ T₁t) | Left ¬T₂t | Left ¬S₂s = function-ok ¬S₂s
  -- r (⟨ s ⟩ ↦ ⟨ t ⟩) (function-ok₂ T₁t) | Left ¬T₂t | Right S₂s = CONTRADICTION (p Q q (s , just t) (Right T₁t) (S₂s , language-comp t ¬T₂t))
  -- r (⟨⟩ ↦ ⟨ t ⟩) (function-ok₂ T₁t) | Left ¬T₂t = CONTRADICTION (p Q q (s₂ , just t) (Right T₁t) (S₂s₂ , language-comp t ¬T₂t))
  -- r (s ↦ ⟨ t ⟩) (function-ok₂ T₁t) | Right T₂t = function-ok₂ T₂t
  -- r (s ↦ diverge) p = ? -- function-diverge

-- A counterexample when the argument type is empty.

set-theoretic-counterexample-one : (∀ Q → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language number))) → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language string))))
set-theoretic-counterexample-one Q q (⟨ scalar s ⟩ , u) Qtu (scalar () , p)

set-theoretic-counterexample-two : (never ⇒ number) ≮: (never ⇒ string)
set-theoretic-counterexample-two = witness (function-ok (scalar number))
                                     (function-ok₀ (scalar-scalar number string (λ ()))) -- witness (function-ok₂ (scalar number)) (function-tgt (scalar-scalar number string (λ ())))
