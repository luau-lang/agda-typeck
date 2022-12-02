{-# OPTIONS --rewriting #-}

module Properties.Subtyping where

open import Agda.Builtin.Equality using (_≡_; refl)
open import FFI.Data.Either using (Either; Left; Right; mapLR; swapLR; cond)
open import FFI.Data.Maybe using (Maybe; just; nothing)
open import Luau.Subtyping using (_<:_; _≮:_; LValue; Language; ¬Language; witness; any; never; scalar; scalar-function; scalar-scalar; scalar-error; function-scalar; function-ok; function-ok₁; function-ok₀; function-error; function-error₀; function-error₁; function-warning₀; function-warning₁; function-nok; function-nerror; function-diverge; left; right; _,_; _↦_; ⟨⟩; ⟨_⟩; error; warning; diverge)
open import Luau.Type using (Type; Scalar; scalar; error; never; unknown; _⇒_; _∪_; _∩_; any; number; string; NIL; NUMBER; STRING; BOOLEAN; _≡ˢ_)
open import Properties.Contradiction using (CONTRADICTION; ¬; ⊥)
open import Properties.Dec using (Dec; yes; no)
open import Properties.Equality using (_≢_)
open import Properties.Functions using (_∘_)
open import Properties.Product using (_×_; _,_)

-- Language membership is decidable
dec-language : ∀ T t → Either (¬Language T t) (Language T t)
dec-language (scalar S) error = Left (scalar-error S)
dec-language (scalar S) ⟨ scalar T ⟩ with T ≡ˢ S 
dec-language (scalar S) ⟨ scalar T ⟩ | yes refl = Right (scalar S)
dec-language (scalar S) ⟨ scalar T ⟩ | no p = Left (scalar-scalar T S p)
dec-language (scalar S) ⟨ s ↦ t ⟩ = Left (scalar-function S)
dec-language (T₁ ⇒ T₂) ⟨ scalar s ⟩ = Left (function-scalar s)
dec-language (T₁ ⇒ T₂) ⟨ ⟨ s ⟩ ↦ ⟨ t ⟩ ⟩ = cond (Right ∘ function-nok) (λ p → mapLR (function-ok₁ p) function-ok (dec-language T₂ ⟨ t ⟩)) (dec-language T₁ ⟨ s ⟩)
dec-language (T₁ ⇒ T₂) ⟨ ⟨ s ⟩ ↦ diverge ⟩ = cond (Right ∘ function-nok) (λ _ → Right function-diverge) (dec-language T₁ ⟨ s ⟩)
dec-language (T₁ ⇒ T₂) ⟨ ⟨ s ⟩ ↦ error ⟩ = cond (Right ∘ function-nok) (λ p → mapLR (function-error₁ p) function-error (dec-language T₂ error)) (dec-language T₁ ⟨ s ⟩)
dec-language (T₁ ⇒ T₂) ⟨ ⟨⟩ ↦ error ⟩ = mapLR function-error₀ function-error (dec-language T₂ error)
dec-language (T₁ ⇒ T₂) ⟨ ⟨⟩ ↦ diverge ⟩ = Right function-diverge
dec-language (T₁ ⇒ T₂) ⟨ ⟨⟩ ↦ ⟨ t ⟩ ⟩ = mapLR function-ok₀ function-ok (dec-language T₂ ⟨ t ⟩)
dec-language never t = Left never
dec-language any t = Right any
dec-language (T₁ ∪ T₂) t = cond (λ p → mapLR (_,_ p) right (dec-language T₂ t)) (Right ∘ left) (dec-language T₁ t)
dec-language (T₁ ∩ T₂) t = cond (Left ∘ left) (λ p → cond (Left ∘ right) (Right ∘ _,_ p) (dec-language T₂ t)) (dec-language T₁ t)
dec-language (T ⇒ T₁) error = Left function-error
dec-language error error = Right error
dec-language error ⟨ t ⟩ = Left error
dec-language (T₁ ⇒ T₂) ⟨ ⟨⟩ ↦ warning ⟩ = cond (Right ∘ function-nerror) (Left ∘ function-warning₀) (dec-language T₁ error)
dec-language (T₁ ⇒ T₂) ⟨ ⟨ s ⟩ ↦ warning ⟩ = cond (Right ∘ function-nok) (Left ∘ function-warning₁) (dec-language T₁ ⟨ s ⟩)

-- ¬Language T is the complement of Language T
language-comp : ∀ {T t} → ¬Language T t → ¬(Language T t)
language-comp (p₁ , p₂) (left q) = language-comp p₁ q
language-comp (p₁ , p₂) (right q) = language-comp p₂ q
language-comp (left p) (q₁ , q₂) = language-comp p q₁
language-comp (right p) (q₁ , q₂) = language-comp p q₂
language-comp (scalar-scalar s p₁ p₂) (scalar s) = p₂ refl
language-comp (function-ok₀ p) (function-ok q) = language-comp p q
language-comp (function-ok₁ p₁ p₂) (function-nok q) = language-comp q p₁
language-comp (function-ok₁ p₁ p₂) (function-ok q) = language-comp p₂ q
language-comp (function-error₀ p) (function-error q) = language-comp p q
language-comp (function-error₁ p₁ p₂) (function-nok q) = language-comp q p₁
language-comp (function-error₁ p₁ p₂) (function-error q) = language-comp p₂ q
language-comp (function-warning₀ p) (function-nerror q) = language-comp q p
language-comp (function-warning₁ p) (function-nok q) = language-comp q p

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
<:-function p q (function-nerror r) = function-nerror (<:-impl-⊇ p r)

<:-function-∩-∩ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∩ S) ⇒ (T ∩ U))
<:-function-∩-∩ (function-ok p , function-ok q) = function-ok (p , q)
<:-function-∩-∩ (function-nok p , q) = function-nok (left p)
<:-function-∩-∩ (p , function-nok q) = function-nok (right q)
<:-function-∩-∩ (function-error p , function-error q) = function-error (p , q)
<:-function-∩-∩ (function-diverge , q) = function-diverge
<:-function-∩-∩ (function-nerror p , q) = function-nerror (left p)

<:-function-∩-∪ : ∀ {R S T U} → ((R ⇒ T) ∩ (S ⇒ U)) <: ((R ∪ S) ⇒ (T ∪ U))
<:-function-∩-∪ (function-ok p , q) = function-ok (left p)
<:-function-∩-∪ (function-error p , q) = function-error (left p)
<:-function-∩-∪ (function-diverge , q) = function-diverge
<:-function-∩-∪ (function-nok p , function-nok q) = function-nok (p , q)
<:-function-∩-∪ (p , function-ok q) = function-ok (right q)
<:-function-∩-∪ (p , function-error q) = function-error (right q)
<:-function-∩-∪ (p , function-diverge) = function-diverge
<:-function-∩-∪ (function-nerror p , function-nerror q) = function-nerror (p , q)

<:-function-∩ : ∀ {S T U} → ((S ⇒ T) ∩ (S ⇒ U)) <: (S ⇒ (T ∩ U))
<:-function-∩ (function-nok p , q) = function-nok p
<:-function-∩ (function-diverge , q) = function-diverge
<:-function-∩ (p , function-nok x) = function-nok x
<:-function-∩ (function-ok p , function-ok q) = function-ok (p , q)
<:-function-∩ (function-error p , function-error q) = function-error (p , q)
<:-function-∩ (function-nerror p , q) = function-nerror p

<:-function-∪ : ∀ {R S T U} → ((R ⇒ S) ∪ (T ⇒ U)) <: ((R ∩ T) ⇒ (S ∪ U))
<:-function-∪ (left (function-ok p)) = function-ok (left p)
<:-function-∪ (left (function-nok p)) = function-nok (left p)
<:-function-∪ (left (function-error p)) = function-error (left p)
<:-function-∪ (left function-diverge) = function-diverge
<:-function-∪ (left (function-nerror p)) = function-nerror (left p)
<:-function-∪ (right (function-ok p)) = function-ok (right p)
<:-function-∪ (right (function-nok p)) = function-nok (right p)
<:-function-∪ (right (function-error p)) = function-error (right p)
<:-function-∪ (right function-diverge) = function-diverge
<:-function-∪ (right (function-nerror p)) = function-nerror (right p)

<:-function-∪-∩ : ∀ {R S T U} → ((R ∩ S) ⇒ (T ∪ U)) <: ((R ⇒ T) ∪ (S ⇒ U))
<:-function-∪-∩ (function-ok (left p)) = left (function-ok p)
<:-function-∪-∩ (function-ok (right p)) = right (function-ok p)
<:-function-∪-∩ (function-nok (left p)) = left (function-nok p)
<:-function-∪-∩ (function-nok (right p)) = right (function-nok p)
<:-function-∪-∩ (function-error (left p)) = left (function-error p)
<:-function-∪-∩ (function-error (right p)) = right (function-error p)
<:-function-∪-∩ function-diverge = left function-diverge
<:-function-∪-∩ (function-nerror (left p)) = left (function-nerror p)
<:-function-∪-∩ (function-nerror (right p)) = right (function-nerror p)

<:-function-left : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (R <: S)
<:-function-left {R} {S} p {⟨ s ⟩} Rs with dec-language S ⟨ s ⟩
<:-function-left p Rs | Right Ss = Ss
<:-function-left p Rs | Left ¬Ss with p (function-nok {u = warning} ¬Ss)
<:-function-left {_} {_} p {⟨ _ ⟩} Rs | Left ¬Ss | function-nok ¬Rs = CONTRADICTION (language-comp ¬Rs Rs)
<:-function-left {R} {S} p {error} Rs with dec-language S error
<:-function-left {R} {S} p {error} Rs | Right Ss = Ss
<:-function-left {R} {S} p {error} Rs | Left ¬Ss with p (function-nerror ¬Ss)
<:-function-left {R} {S} p {error} Rs | Left ¬Ss | function-nerror ¬Rs = CONTRADICTION (language-comp ¬Rs Rs)

<:-function-right : ∀ {R S T U} → (S ⇒ T) <: (R ⇒ U) → (T <: U)
<:-function-right p {⟨ t ⟩} Tt with p (function-ok {t = ⟨⟩} Tt)
<:-function-right p {⟨ t ⟩} Tt | function-ok Ut = Ut
<:-function-right p {error} Tt with p (function-error {t = ⟨⟩} Tt)
<:-function-right p {error} Tt | function-error Ut = Ut

≮:-function-left : ∀ {R S T U} → (R ≮: S) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-left (witness {error} p q) = witness (function-nerror q) (function-warning₀ p)
≮:-function-left (witness {⟨ s ⟩} p q) = witness (function-nok q) (function-warning₁ p)

≮:-function-right : ∀ {R S T U} → (T ≮: U) → (S ⇒ T) ≮: (R ⇒ U)
≮:-function-right (witness {error} p q) = witness (function-error p) (function-error₀ q)
≮:-function-right (witness {⟨ s ⟩} p q) = witness (function-ok p) (function-ok₀ q)

-- Properties of scalars
scalar-<: : ∀ S {T} → Language T ⟨ scalar S ⟩ → (scalar S <: T)
scalar-<: S p (scalar S) = p

function-∩-scalar-<:-never : ∀ S {T U V} → ((T ⇒ U) ∩ scalar S) <: V
function-∩-scalar-<:-never S (() , scalar S)

error-∩-scalar-<:-never : ∀ S {V} → (error ∩ scalar S) <: V
error-∩-scalar-<:-never S (() , scalar S)

scalar-∩-error-<:-never : ∀ S {V} → (scalar S ∩ error) <: V
scalar-∩-error-<:-never S (() , error)

function-≮:-scalar : ∀ {S T} U → ((S ⇒ T) ≮: scalar U)
function-≮:-scalar S = witness (function-diverge {t = ⟨⟩}) (scalar-function S)

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
function-∩-error-<:-never : ∀ {T U V} → ((T ⇒ U) ∩ error) <: V
function-∩-error-<:-never (() , error)

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
function-≮:-never = witness (function-diverge {t = ⟨⟩}) never

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
<:-everything {⟨ ⟨⟩ ↦ error ⟩} p = left (left (left (left (left (function-error any)))))
<:-everything {⟨ ⟨⟩ ↦ warning ⟩} p = left (left (left (left (left (function-nerror never)))))
<:-everything {⟨ ⟨⟩ ↦ diverge ⟩} p = left (left (left (left (left function-diverge))))
<:-everything {⟨ ⟨⟩ ↦ ⟨ x ⟩ ⟩} p = left (left (left (left (left (function-ok any)))))
<:-everything {⟨ ⟨ s ⟩ ↦ t ⟩} p = left (left (left (left (left (function-nok never)))))

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
  S₂⊆S₁ error S₂t | Left ¬S₁t with p ⟨ ⟨⟩ ↦ warning ⟩ (function-nerror ¬S₁t)
  S₂⊆S₁ error S₂t | Left ¬S₁t | function-nerror ¬S₂t = CONTRADICTION (language-comp ¬S₂t S₂t)
  S₂⊆S₁ ⟨ t ⟩ S₂t | Left ¬S₁t with p ⟨ ⟨ t ⟩ ↦ warning ⟩ (function-nok ¬S₁t)
  S₂⊆S₁ ⟨ t ⟩ S₂t | Left ¬S₁t | function-nok ¬S₂t = CONTRADICTION (language-comp ¬S₂t S₂t)
  S₂⊆S₁ t S₂t | Right S₁t = S₁t
  
  ¬T₂⊆¬T₁ : Comp(Lift(Language T₂)) ⊆ Comp(Lift(Language T₁))
  ¬T₂⊆¬T₁ (just ⟨ u ⟩) ¬T₂u T₁u with p ⟨ ⟨⟩ ↦ ⟨ u ⟩ ⟩ (function-ok T₁u)
  ¬T₂⊆¬T₁ (just ⟨ u ⟩) ¬T₂u T₁u | function-ok T₂u = ¬T₂u T₂u
  ¬T₂⊆¬T₁ (just error) ¬T₂u T₁u with p ⟨ ⟨⟩ ↦ error ⟩ (function-error T₁u)
  ¬T₂⊆¬T₁ (just error) ¬T₂u T₁u | function-error T₂u = ¬T₂u T₂u

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
  r ⟨ ⟨ s ⟩ ↦ t ⟩ (function-nok ¬S₁s) = function-nok (¬S₁⊆¬S₂ ⟨ s ⟩ ¬S₁s)
  r ⟨ ⟨⟩ ↦ warning ⟩ (function-nerror ¬S₁e) = function-nerror (¬S₁⊆¬S₂ error ¬S₁e)
  r ⟨ s ↦ ⟨ t ⟩ ⟩ (function-ok T₁t) = function-ok (T₁⊆T₂ ⟨ t ⟩ T₁t)
  r ⟨ s ↦ error ⟩ (function-error T₁e) = function-error (T₁⊆T₂ error T₁e)
  r ⟨ s ↦ diverge ⟩ function-diverge = function-diverge

-- A counterexample when the argument type is empty.

set-theoretic-counterexample-one : (∀ Q → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language number))) → Q ⊆ Comp((Language never) ⊗ Comp(Lift(Language string))))
set-theoretic-counterexample-one Q q (⟨ scalar s ⟩ , u) Qtu (() , p)

set-theoretic-counterexample-two : (never ⇒ number) ≮: (never ⇒ string)
set-theoretic-counterexample-two = witness (function-ok (scalar NUMBER))
                                     (function-ok₀ (scalar-scalar NUMBER STRING (λ ())))
