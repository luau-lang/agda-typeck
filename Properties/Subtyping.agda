{-# OPTIONS --rewriting #-}

module Properties.Subtyping where

open import Agda.Builtin.Equality using (_≡_; refl)
open import FFI.Data.Either using (Either; Left; Right; mapLR; swapLR; cond)
open import FFI.Data.Maybe using (Maybe; just; nothing)
open import Luau.Subtyping using (_<:_; _≮:_; Value; Language; ¬Language; ALanguage; ¬ALanguage; RLanguage; ¬RLanguage; witness; any; never; scalar; scalar-function; scalar-scalar; scalar-error; scalar-warning; function-scalar; function-ok; function-nok; function-error; function-function; function-warning; left; right; _,_; _↦_; ⟨⟩; ⟨_⟩; error; warning; diverge; ⟨untyped⟩; one; none; untyped)
open import Luau.Type using (Type; Scalar; scalar; error; never; unknown; funktion;_⇒_; _∪_; _∩_; any; number; string; NIL; NUMBER; STRING; BOOLEAN; _≡ˢ_)
open import Properties.Contradiction using (CONTRADICTION; ¬; ⊥)
open import Properties.Dec using (Dec; yes; no)
open import Properties.Equality using (_≢_)
open import Properties.Functions using (_∘_)
open import Properties.Product using (_×_; _,_)

-- Language membership is decidable
dec-language : ∀ T t → Either (¬Language T t) (Language T t)
dec-alanguage : ∀ T t → Either (¬ALanguage T t) (ALanguage T t)
dec-rlanguage : ∀ T t → Either (¬RLanguage T t) (RLanguage T t)

dec-language (scalar S) error = Left (scalar-error S)
dec-language (scalar S) ⟨ scalar T ⟩ with T ≡ˢ S 
dec-language (scalar S) ⟨ scalar T ⟩ | yes refl = Right (scalar S)
dec-language (scalar S) ⟨ scalar T ⟩ | no p = Left (scalar-scalar T S p)
dec-language (scalar S) ⟨ s ↦ t ⟩ = Left (scalar-function S)
dec-language (S ⇒ T) ⟨ scalar s ⟩ = Left (function-scalar s)
dec-language (S ⇒ T) ⟨ s ↦ t ⟩ = cond (Right ∘ function-nok) (λ p → mapLR (function-function p) function-ok (dec-rlanguage T t)) (dec-alanguage S s)
dec-language never t = Left never
dec-language any t = Right any
dec-language (S ∪ T) t = cond (λ p → mapLR (_,_ p) right (dec-language T t)) (Right ∘ left) (dec-language S t)
dec-language (S ∩ T) t = cond (Left ∘ left) (λ p → mapLR right (_,_ p) (dec-language T t)) (dec-language S t)
dec-language (T ⇒ T₁) error = Left function-error
dec-language error error = Right error
dec-language error ⟨ t ⟩ = Left error
dec-language (scalar S) ⟨ warning t ⟩ = Left scalar-warning
dec-language (S ⇒ T) ⟨ warning t ⟩ = cond (Right ∘ function-warning) (Left ∘ function-warning) (dec-language S t)

dec-alanguage T ⟨⟩ = Right none
dec-alanguage T ⟨untyped⟩ = mapLR untyped untyped (dec-language T error)
dec-alanguage T ⟨ t ⟩ = mapLR one one (dec-language T ⟨ t ⟩)

dec-rlanguage T error = mapLR error error (dec-language T error)
dec-rlanguage T diverge = Right diverge
dec-rlanguage T ⟨ t ⟩ = mapLR one one (dec-language T ⟨ t ⟩)

-- ¬Language T is the complement of Language T
language-comp : ∀ {T t} → ¬Language T t → ¬(Language T t)
language-comp (p₁ , p₂) (left q) = language-comp p₁ q
language-comp (p₁ , p₂) (right q) = language-comp p₂ q
language-comp (left p) (q₁ , q₂) = language-comp p q₁
language-comp (right p) (q₁ , q₂) = language-comp p q₂
language-comp (scalar-scalar s p₁ p₂) (scalar s) = p₂ refl
language-comp (function-function (untyped p₁) p₂) (function-nok (untyped q)) = language-comp q p₁
language-comp (function-function (one p₁) p₂) (function-nok (one q)) = language-comp q p₁
language-comp (function-function p₁ (error p₂)) (function-ok (error q)) = language-comp p₂ q
language-comp (function-function p₁ (one p₂)) (function-ok (one q)) = language-comp p₂ q
language-comp (function-warning p) (function-warning q) = language-comp q p

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
<:-function p q (function-ok (error r)) = function-ok (error (q r))
<:-function p q (function-ok diverge) = function-ok diverge
<:-function p q (function-ok (one r)) = function-ok (one (q r))
<:-function p q (function-nok (untyped r)) = function-nok (untyped (<:-impl-⊇ p r))
<:-function p q (function-nok (one r)) = function-nok (one (<:-impl-⊇ p r))
<:-function p q (function-warning r) = function-warning (<:-impl-⊇ p r)

<:-function-∩-∩ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∩ S) ⇒ (T ∩ U))
<:-function-∩-∩ (p , function-ok diverge) = function-ok diverge
<:-function-∩-∩ (function-nok (untyped p) , q) = function-nok (untyped (left p))
<:-function-∩-∩ (function-nok (one p) , q) = function-nok (one (left p))
<:-function-∩-∩ (p , function-nok (untyped q)) = function-nok (untyped (right q))
<:-function-∩-∩ (p , function-nok (one q)) = function-nok (one (right q))
<:-function-∩-∩ (function-ok (error p) , function-ok (error q)) = function-ok (error (p , q))
<:-function-∩-∩ (function-ok (one p) , function-ok (one q)) = function-ok (one (p , q))
<:-function-∩-∩ (function-warning p , q) = function-warning (left p)

<:-function-∩-∪ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∪ S) ⇒ (T ∪ U))
<:-function-∩-∪ (p , function-ok (error q)) = function-ok (error (right q))
<:-function-∩-∪ (p , function-ok diverge) = function-ok diverge
<:-function-∩-∪ (p , function-ok (one q)) = function-ok (one (right q))
<:-function-∩-∪ (function-nok (untyped p) , function-nok (untyped q)) = function-nok (untyped (p , q))
<:-function-∩-∪ (function-nok (one p) , function-nok (one q)) = function-nok (one (p , q))
<:-function-∩-∪ (function-ok (error p) , q) = function-ok (error (left p))
<:-function-∩-∪ (function-ok diverge , q) = function-ok diverge
<:-function-∩-∪ (function-ok (one p) , q) = function-ok (one (left p))
<:-function-∩-∪ (function-warning p , function-warning q) = function-warning (p , q)

<:-function-∩ : ∀ {S T U} → ((S ⇒ T) ∩ (S ⇒ U)) <: (S ⇒ (T ∩ U))
<:-function-∩ (function-nok p , q) = function-nok p
<:-function-∩ (p , function-nok q) = function-nok q
<:-function-∩ (function-ok (error p) , function-ok (error q)) = function-ok (error (p , q))
<:-function-∩ (function-ok diverge , q) = function-ok diverge
<:-function-∩ (function-ok (one p) , function-ok (one q)) = function-ok (one (p , q))
<:-function-∩ (function-warning p , q) = function-warning p

<:-function-∪ : ∀ {R S T U} → ((R ⇒ S) ∪ (T ⇒ U)) <: ((R ∩ T) ⇒ (S ∪ U))
<:-function-∪ (left (function-nok (untyped p))) = function-nok (untyped (left p))
<:-function-∪ (left (function-nok (one p))) = function-nok (one (left p))
<:-function-∪ (left (function-ok (error p))) = function-ok (error (left p))
<:-function-∪ (left (function-ok diverge)) = function-ok diverge
<:-function-∪ (left (function-ok (one p))) = function-ok (one (left p))
<:-function-∪ (left (function-warning p)) = function-warning (left p)
<:-function-∪ (right (function-nok (untyped p))) = function-nok (untyped (right p))
<:-function-∪ (right (function-nok (one p))) = function-nok (one (right p))
<:-function-∪ (right (function-ok (error p))) = function-ok (error (right p))
<:-function-∪ (right (function-ok diverge)) = function-ok diverge
<:-function-∪ (right (function-ok (one p))) = function-ok (one (right p))
<:-function-∪ (right (function-warning p)) = function-warning (right p)

<:-function-∪-∩ : ∀ {R S T U} → ((R ∩ S) ⇒ (T ∪ U)) <: ((R ⇒ T) ∪ (S ⇒ U))
<:-function-∪-∩ (function-nok (untyped (left p))) = left (function-nok (untyped p))
<:-function-∪-∩ (function-nok (untyped (right p))) = right (function-nok (untyped p))
<:-function-∪-∩ (function-nok (one (left p))) = left (function-nok (one p))
<:-function-∪-∩ (function-nok (one (right p))) = right (function-nok (one p))
<:-function-∪-∩ (function-ok (error (left p))) = left (function-ok (error p))
<:-function-∪-∩ (function-ok (error (right p))) = right (function-ok (error p))
<:-function-∪-∩ (function-ok diverge) = left (function-ok diverge)
<:-function-∪-∩ (function-ok (one (left p))) = left (function-ok (one p))
<:-function-∪-∩ (function-ok (one (right p))) = right (function-ok (one p))
<:-function-∪-∩ (function-warning (left p)) = left (function-warning p)
<:-function-∪-∩ (function-warning (right p)) = right (function-warning p)

<:-function-left : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (R <: S)
<:-function-left {R} {S} p {error} Rs with dec-language S error
<:-function-left {R} {S} p {error} Re | Right Se = Se
<:-function-left {R} {S} p {error} Re | Left ¬Se with p (function-warning ¬Se)
<:-function-left {R} {S} p {error} Re | Left ¬Se | function-warning ¬Re = CONTRADICTION (language-comp ¬Re Re)
<:-function-left {R} {S} p {⟨ s ⟩} Rs with dec-language S ⟨ s ⟩
<:-function-left {R} {S} p {⟨ s ⟩} Rs | Right Ss = Ss
<:-function-left {R} {S} p {⟨ s ⟩} Rs | Left ¬Ss with p (function-warning ¬Ss)
<:-function-left {R} {S} p {⟨ s ⟩} Rs | Left ¬Ss | function-warning ¬Rs = CONTRADICTION (language-comp ¬Rs Rs)

<:-function-right : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (T <: U)
<:-function-right p {error} Te with p (function-ok {t = ⟨⟩} (error Te))
<:-function-right p {error} Te | function-ok (error Ue) = Ue
<:-function-right p {⟨ t ⟩} Tt with p (function-ok {t = ⟨⟩} (one Tt))
<:-function-right p {⟨ t ⟩} Tt | function-ok (one Ut) = Ut

≮:-function-left : ∀ {R S T U} → (R ≮: S) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-left (witness p q) = witness (function-warning q) (function-warning p)

≮:-function-right : ∀ {R S T U} → (T ≮: U) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-right (witness {error} p q) = witness (function-ok (error p)) (function-function none (error q))
≮:-function-right (witness {⟨ s ⟩} p q) = witness (function-ok (one p)) (function-function none (one q))

function-<:-funktion : ∀ {S T} → (S ⇒ T) <: funktion
function-<:-funktion = <:-function (λ ()) (λ p → any)

function-<:-unknown : ∀ {S T} → (S ⇒ T) <: unknown
function-<:-unknown p = left (left (left (left (function-<:-funktion p))))

error-≮:-function : ∀ {S T} → error ≮: (S ⇒ T)
error-≮:-function = witness error function-error

-- Properties of scalars
scalar-<: : ∀ S {T} → Language T ⟨ scalar S ⟩ → (scalar S <: T)
scalar-<: S p (scalar S) = p

scalar-<:-unknown : ∀ {S} → (scalar S <: unknown)
scalar-<:-unknown {NUMBER} p = left (left (left (right p)))
scalar-<:-unknown {BOOLEAN} p = right p
scalar-<:-unknown {STRING} p = left (left (right p))
scalar-<:-unknown {NIL} p = left (right p)

function-∩-scalar-<:-never : ∀ S {T U V} → ((T ⇒ U) ∩ scalar S) <: V
function-∩-scalar-<:-never S (() , scalar S)

error-∩-scalar-<:-never : ∀ S {V} → (error ∩ scalar S) <: V
error-∩-scalar-<:-never S (() , scalar S)

scalar-∩-error-<:-never : ∀ S {V} → (scalar S ∩ error) <: V
scalar-∩-error-<:-never S (() , error)

function-≮:-scalar : ∀ {S T} U → ((S ⇒ T) ≮: scalar U)
function-≮:-scalar S = witness (function-ok {t = ⟨⟩} diverge) (scalar-function S)

error-≮:-scalar : ∀ S → (error ≮: scalar S)
error-≮:-scalar S = witness error (scalar-error S)

scalar-≮:-function : ∀ {S T} U → (scalar U ≮: (S ⇒ T))
scalar-≮:-function S = witness (scalar S) (function-scalar S)

any-≮:-scalar : ∀ U → (any ≮: scalar U)
any-≮:-scalar s = witness any (scalar-function s {t = ⟨⟩} {u = diverge})

scalar-≮:-never : ∀ U → (scalar U ≮: never)
scalar-≮:-never s = witness (scalar s) never

scalar-≢-impl-≮: : ∀ T U → (T ≢ U) → (scalar T ≮: scalar U)
scalar-≢-impl-≮: s₁ s₂ p = witness (scalar s₁) (scalar-scalar s₁ s₂ p)

scalar-≢-∩-<:-never : ∀ T U {V} → (T ≢ U) → (scalar T ∩ scalar U) <: V
scalar-≢-∩-<:-never s t p (scalar s₁ , scalar s₂) = CONTRADICTION (p refl)

-- Properties of error
error-<: : ∀ {T} → Language T error → (error <: T)
error-<: p error = p

function-∩-error-<:-never : ∀ {T U V} → ((T ⇒ U) ∩ error) <: V
function-∩-error-<:-never (() , error)

error-≮:-never : error ≮: never
error-≮:-never = witness error never

-- Properties of any and never
any-≮: : ∀ {T U} → (T ≮: U) → (any ≮: U)
any-≮: (witness p q) = witness any q

never-≮: : ∀ {T U} → (T ≮: U) → (T ≮: never)
never-≮: (witness p q) = witness p never

any-≮:-never : (any ≮: never)
any-≮:-never = witness {t = ⟨ scalar NIL ⟩} any never

any-≮:-function : ∀ {S T} → (any ≮: (S ⇒ T))
any-≮:-function = witness any (function-scalar NIL)

function-≮:-never : ∀ {T U} → ((T ⇒ U) ≮: never)
function-≮:-never = witness (function-ok {t = ⟨⟩} diverge) never

<:-never : ∀ {T} → (never <: T)
<:-never ()

≮:-never-left : ∀ {S T U} → (S <: (T ∪ U)) → (S ≮: T) → (S ∩ U) ≮: never
≮:-never-left p (witness q₁ q₂) with p q₁
≮:-never-left p (witness q₁ q₂) | left r = CONTRADICTION (language-comp q₂ r)
≮:-never-left p (witness q₁ q₂) | right r = witness (q₁ , r) never

≮:-never-right : ∀ {S T U} → (S <: (T ∪ U)) → (S ≮: U) → (S ∩ T) ≮: never
≮:-never-right p (witness q₁ q₂) with p q₁
≮:-never-right p (witness q₁ q₂) | left r = witness (q₁ , r) never
≮:-never-right p (witness q₁ q₂) | right r = CONTRADICTION (language-comp q₂ r)

<:-any : ∀ {T} → (T <: any)
<:-any p = any

<:-everything : any <: (unknown ∪ error)
<:-everything {error} p = right error
<:-everything {⟨ scalar NUMBER ⟩} p = left (left (left (left (right (scalar NUMBER)))))
<:-everything {⟨ scalar BOOLEAN ⟩} p = left (right (scalar BOOLEAN))
<:-everything {⟨ scalar STRING ⟩} p = left (left (left (right (scalar STRING))))
<:-everything {⟨ scalar NIL ⟩} p = left (left (right (scalar NIL)))
<:-everything {⟨ warning t ⟩} p = left (left (left (left (left (function-warning never)))))
<:-everything {⟨ ⟨⟩ ↦ error ⟩} p = left (left (left (left (left (function-ok (error any))))))
<:-everything {⟨ ⟨⟩ ↦ diverge ⟩} p = left (left (left (left (left (function-ok diverge)))))
<:-everything {⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩} p = left (left (left (left (left (function-ok (one any))))))
<:-everything {⟨ ⟨untyped⟩ ↦ t ⟩} p = left (left (left (left (left (function-nok (untyped never))))))
<:-everything {⟨ ⟨ s ⟩ ↦ t ⟩} p = left (left (left (left (left (function-nok (one never))))))

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

set-theoretic-if {S₁} {T₁} {S₂} {T₂} p Q q (t , u) Qtu (S₂t , ¬T₂u) = q (t , u) Qtu (S₂⊆S₁ t S₂t , ¬T₂⊆¬T₁ u ¬T₂u) where

  S₂⊆S₁ : Language S₂ ⊆ Language S₁
  S₂⊆S₁ t S₂t with dec-language S₁ t
  S₂⊆S₁ t S₂t | Left ¬S₁t with p ⟨ warning t ⟩ (function-warning ¬S₁t)
  S₂⊆S₁ t S₂t | Left ¬S₁t | function-warning ¬S₂t = CONTRADICTION (language-comp ¬S₂t S₂t)
  S₂⊆S₁ t S₂t | Right S₁t = S₁t
  
  ¬T₂⊆¬T₁ : Comp(Lift(Language T₂)) ⊆ Comp(Lift(Language T₁))
  ¬T₂⊆¬T₁ (just ⟨ u ⟩) ¬T₂u T₁u with p ⟨ ⟨⟩ ↦ ⟨ u ⟩ ⟩ (function-ok (one T₁u))
  ¬T₂⊆¬T₁ (just ⟨ u ⟩) ¬T₂u T₁u | function-ok (one T₂u) = ¬T₂u T₂u
  ¬T₂⊆¬T₁ (just error) ¬T₂u T₁u with p ⟨ ⟨⟩ ↦ error ⟩ (function-ok (error T₁u))
  ¬T₂⊆¬T₁ (just error) ¬T₂u T₁u | function-ok (error T₂e) = ¬T₂u T₂e

not-quite-set-theoretic-only-if : ∀ {S₁ T₁ S₂ T₂} →

  -- We don't quite have that this is a set-theoretic model
  -- it's only true when Language S₂ is inhabited
  -- in particular it's not true when S₂ is never,
  ∀ s₂ → Language S₂ s₂ →

  -- This is the "only if" part of being a set-theoretic model
  (∀ Q → Q ⊆ Comp((Language S₁) ⊗ Comp(Lift(Language T₁))) → Q ⊆ Comp((Language S₂) ⊗ Comp(Lift(Language T₂)))) →
  (Language (S₁ ⇒ T₁) ⊆ Language (S₂ ⇒ T₂))

not-quite-set-theoretic-only-if {S₁} {T₁} {S₂} {T₂} s₂ S₂s₂ p = r where

  Q : (Value × Maybe Value) → Set
  Q (t , just u) = Either (¬Language S₁ t) (Language T₁ u)
  Q (t , nothing) = ¬Language S₁ t
  
  q : Q ⊆ Comp(Language S₁ ⊗ Comp(Lift(Language T₁)))
  q (t , just u) (Left ¬S₁t) (S₁t , ¬T₁u) = language-comp ¬S₁t S₁t
  q (t , just u) (Right T₂u) (S₁t , ¬T₁u) = ¬T₁u T₂u
  q (t , nothing) ¬S₁t (S₁t , _) = language-comp ¬S₁t S₁t

  ¬S₁⊆¬S₂ : ¬Language S₁ ⊆ ¬Language S₂
  ¬S₁⊆¬S₂ s ¬S₁s with dec-language S₂ s
  ¬S₁⊆¬S₂ s ¬S₁s | Left ¬S₂s = ¬S₂s
  ¬S₁⊆¬S₂ s ¬S₁s | Right S₂s = CONTRADICTION (p Q q (s , nothing) ¬S₁s (S₂s , λ ()))

  T₁⊆T₂ : Language T₁ ⊆ Language T₂
  T₁⊆T₂ t T₁t with dec-language T₂ t
  T₁⊆T₂ t T₁t | Left ¬T₂t = CONTRADICTION (p Q q (s₂ , just t) (Right T₁t) (S₂s₂ , language-comp ¬T₂t)) 
  T₁⊆T₂ t T₁t | Right T₂t = T₂t

  r : Language (S₁ ⇒ T₁) ⊆ Language (S₂ ⇒ T₂)
  r ⟨ warning s ⟩ (function-warning ¬S₁s) = function-warning (¬S₁⊆¬S₂ s ¬S₁s)
  r ⟨ ⟨ s ⟩ ↦ t ⟩ (function-nok (one ¬S₁s)) = function-nok (one (¬S₁⊆¬S₂ ⟨ s ⟩ ¬S₁s))
  r ⟨ s ↦ ⟨ t ⟩ ⟩ (function-ok (one T₁t)) = function-ok (one (T₁⊆T₂ ⟨ t ⟩ T₁t))
  r ⟨ ⟨untyped⟩ ↦ t ⟩ (function-nok (untyped ¬S₁e)) = function-nok (untyped (¬S₁⊆¬S₂ error ¬S₁e))
  r ⟨ s ↦ error ⟩ (function-ok (error T₁e)) = function-ok (error (T₁⊆T₂ error T₁e))
  r ⟨ s ↦ diverge ⟩ p = function-ok diverge

-- A counterexample when the argument type is empty.

set-theoretic-counterexample-one : (∀ Q → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language number))) → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language string))))
set-theoretic-counterexample-one Q q (⟨ scalar s ⟩ , u) Qtu (() , p)

set-theoretic-counterexample-two : (never ⇒ number) ≮: (never ⇒ string)
set-theoretic-counterexample-two = witness (function-ok (one (scalar NUMBER)))
                                     (function-function none (one (scalar-scalar NUMBER STRING (λ ()))))
