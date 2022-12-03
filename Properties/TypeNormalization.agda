{-# OPTIONS --rewriting #-}

module Properties.TypeNormalization where

open import Agda.Builtin.Equality using (refl)
open import Luau.Type using (Type; Scalar; nil; number; string; boolean; error; never; any; unknown; scalar; _⇒_; _∪_; _∩_; NIL; NUMBER; STRING; BOOLEAN; _≡ˢ_; _≡ᵀ_)
open import Luau.Subtyping using (Language; ¬Language; scalar; any; left; right; function-ok; function-error; function-nok; function-nerror; function-diverge; scalar-function; function-scalar; _,_; _↦_; ⟨⟩; ⟨_⟩; error; diverge)
open import Luau.TypeNormalization using (_∪ⁿ_; _∩ⁿ_; _∪ᶠ_; _∪ⁿˢ_; _∩ⁿˢ_; normalize)
open import Luau.Subtyping using (_<:_; _≮:_; witness; never)
open import Properties.Dec using (Dec; yes; no)
open import Properties.Subtyping using (<:-trans; <:-refl; <:-any; <:-never; <:-∪-left; <:-∪-right; <:-∪-lub; <:-∩-left; <:-∩-right; <:-∩-glb; <:-∩-symm; <:-function; <:-function-∪-∩; <:-function-∩-∪; <:-function-∪; <:-everything; <:-union; <:-∪-assocl; <:-∪-assocr; <:-∪-symm; <:-intersect;  ∪-distl-∩-<:; ∪-distr-∩-<:; <:-∪-distr-∩; <:-∪-distl-∩; ∩-distl-∪-<:; <:-∩-distl-∪; <:-∩-distr-∪; function-∩-scalar-<:-never; function-∩-error-<:-never; error-∩-scalar-<:-never; scalar-∩-error-<:-never; scalar-≢-∩-<:-never)

data ErrScalar : Type → Set where
  error : ErrScalar error
  scalar : ∀ S → ErrScalar (scalar S)

-- Normal forms for types
data FunType : Type → Set
data Normal : Type → Set

data FunType where
  _⇒_ : ∀ S T → FunType (S ⇒ T)
  _∩_ : ∀ {F G} → FunType F → FunType G → FunType (F ∩ G)

data Normal where
  _⇒_ : ∀ S T → Normal (S ⇒ T)
  _∩_ : ∀ {F G} → FunType F → FunType G → Normal (F ∩ G)
  _∪_ : ∀ {S T} → Normal S → ErrScalar T → Normal (S ∪ T)
  never : Normal never

data OptScalar : Type → Set where
  never : OptScalar never
  error : OptScalar error
  scalar : ∀ S → OptScalar (scalar S)

-- Top function type
fun-top : ∀ {F} → (FunType F) → (F <: (never ⇒ any))
fun-top (S ⇒ T) = <:-function <:-never <:-any
fun-top (F ∩ G) = <:-trans <:-∩-left (fun-top F)

-- function types are inhabited
fun-function : ∀ {F} → FunType F → Language F ⟨ ⟨⟩ ↦ diverge ⟩
fun-function (S ⇒ T) = function-diverge
fun-function (F ∩ G) = (fun-function F , fun-function G)

fun-≮:-never : ∀ {F} → FunType F → (F ≮: never)
fun-≮:-never F = witness (fun-function F) never

-- function types aren't scalars
fun-¬scalar : ∀ S {F t} → FunType F → Language F t → ¬Language (scalar S) t
fun-¬scalar s (S ⇒ T) (function-nok x) = scalar-function s
fun-¬scalar s (S ⇒ T) (function-nerror x) = scalar-function s
fun-¬scalar s (S ⇒ T) (function-ok p) = scalar-function s
fun-¬scalar s (S ⇒ T) (function-error p) = scalar-function s
fun-¬scalar s (S ⇒ T) function-diverge = scalar-function s
fun-¬scalar s (F ∩ G) (p , q) = fun-¬scalar s G q

¬scalar-fun : ∀ {F} → FunType F → ∀ S → ¬Language F ⟨ scalar S ⟩
¬scalar-fun (S ⇒ T) s = function-scalar s
¬scalar-fun (F ∩ G) s = left (¬scalar-fun F s)

scalar-≮:-fun : ∀ {F} → FunType F → ∀ S → scalar S ≮: F
scalar-≮:-fun F s = witness (scalar s) (¬scalar-fun F s)

-- function types aren't errors
fun-¬error : ∀ {F t} → FunType F → Language F t → ¬Language error t
fun-¬error (S ⇒ T) (function-nok p) = error
fun-¬error (S ⇒ T) (function-nerror p) = error
fun-¬error (S ⇒ T) (function-ok p) = error
fun-¬error (S ⇒ T) (function-error p) = error
fun-¬error (S ⇒ T) function-diverge = error
fun-¬error (F ∩ G) (p , q) = fun-¬error G q

¬error-fun : ∀ {F} → FunType F → ¬Language F error
¬error-fun (S ⇒ T) = function-error
¬error-fun (F ∩ G) = left (¬error-fun F)

error-≮:-fun : ∀ {F} → FunType F → error ≮: F
error-≮:-fun F = witness error (¬error-fun F)

-- unknown is normal
normal-unknown : Normal unknown
normal-unknown = ((((never ⇒ any) ∪ scalar NUMBER) ∪ scalar STRING) ∪ scalar NIL) ∪ scalar BOOLEAN

-- Normalization produces normal types
normal : ∀ T → Normal (normalize T)
normalᶠ : ∀ {F} → FunType F → Normal F
normal-∪ⁿ : ∀ {S T} → Normal S → Normal T → Normal (S ∪ⁿ T)
normal-∩ⁿ : ∀ {S T} → Normal S → Normal T → Normal (S ∩ⁿ T)
normal-∪ⁿˢ : ∀ {S T} → Normal S → OptScalar T → Normal (S ∪ⁿˢ T)
normal-∩ⁿˢ : ∀ {S T} → Normal S → ErrScalar T → OptScalar (S ∩ⁿˢ T)
normal-∪ᶠ : ∀ {F G} → FunType F → FunType G → FunType (F ∪ᶠ G)

normal (scalar S) = never ∪ scalar S
normal (S ⇒ T) = S ⇒ T
normal never = never
normal any = normal-unknown ∪ error
normal error = never ∪ error
normal (S ∪ T) = normal-∪ⁿ (normal S) (normal T)
normal (S ∩ T) = normal-∩ⁿ (normal S) (normal T)

normalᶠ (S ⇒ T) = S ⇒ T
normalᶠ (F ∩ G) = F ∩ G

normal-∪ⁿ S (T₁ ∪ T₂) = (normal-∪ⁿ S T₁) ∪ T₂
normal-∪ⁿ S never = S
normal-∪ⁿ never (T ⇒ U) = T ⇒ U
normal-∪ⁿ never (G₁ ∩ G₂) = G₁ ∩ G₂
normal-∪ⁿ (R ⇒ S) (T ⇒ U) = normalᶠ (normal-∪ᶠ (R ⇒ S) (T ⇒ U))
normal-∪ⁿ (R ⇒ S) (G₁ ∩ G₂) = normalᶠ (normal-∪ᶠ (R ⇒ S) (G₁ ∩ G₂))
normal-∪ⁿ (F₁ ∩ F₂) (T ⇒ U) = normalᶠ (normal-∪ᶠ (F₁ ∩ F₂) (T ⇒ U))
normal-∪ⁿ (F₁ ∩ F₂) (G₁ ∩ G₂) = normalᶠ (normal-∪ᶠ (F₁ ∩ F₂) (G₁ ∩ G₂))
normal-∪ⁿ (S₁ ∪ S₂) (T₁ ⇒ T₂) = normal-∪ⁿ S₁ (T₁ ⇒ T₂) ∪ S₂
normal-∪ⁿ (S₁ ∪ S₂) (G₁ ∩ G₂) = normal-∪ⁿ S₁ (G₁ ∩ G₂) ∪ S₂

normal-∩ⁿ S never = never
normal-∩ⁿ S (T ∪ U) = normal-∪ⁿˢ (normal-∩ⁿ S T) (normal-∩ⁿˢ S U )
normal-∩ⁿ never (T ⇒ U) = never
normal-∩ⁿ (R ⇒ S) (T ⇒ U) = (R ⇒ S) ∩ (T ⇒ U)
normal-∩ⁿ (R ∩ S) (T ⇒ U) = (R ∩ S) ∩ (T ⇒ U)
normal-∩ⁿ (R ∪ S) (T ⇒ U) = normal-∩ⁿ R (T ⇒ U)
normal-∩ⁿ never (T ∩ U) = never
normal-∩ⁿ (R ⇒ S) (T ∩ U) = (R ⇒ S) ∩ (T ∩ U)
normal-∩ⁿ (R ∩ S) (T ∩ U) = (R ∩ S) ∩ (T ∩ U)
normal-∩ⁿ (R ∪ S) (T ∩ U) = normal-∩ⁿ R (T ∩ U)

normal-∪ⁿˢ S never = S
normal-∪ⁿˢ never (scalar T) = never ∪ (scalar T)
normal-∪ⁿˢ (R ⇒ S) (scalar T) = (R ⇒ S) ∪ (scalar T)
normal-∪ⁿˢ (R ∩ S) (scalar T) = (R ∩ S) ∪ (scalar T)
normal-∪ⁿˢ (R ∪ scalar S) (scalar T) with S ≡ˢ T
normal-∪ⁿˢ (R ∪ scalar S) (scalar T) | yes refl = R ∪ scalar S
normal-∪ⁿˢ (R ∪ scalar S) (scalar T) | no p = normal-∪ⁿˢ R (scalar T) ∪ scalar S
normal-∪ⁿˢ (R ∪ error) (scalar T) = normal-∪ⁿˢ R (scalar T) ∪ error
normal-∪ⁿˢ (R ⇒ S) error = (R ⇒ S) ∪ error
normal-∪ⁿˢ (F ∩ G) error = (F ∩ G) ∪ error
normal-∪ⁿˢ (R ∪ error) error = R ∪ error
normal-∪ⁿˢ (R ∪ scalar S) error = normal-∪ⁿˢ R error ∪ scalar S
normal-∪ⁿˢ never error = never ∪ error

normal-∩ⁿˢ never (scalar T) = never
normal-∩ⁿˢ never error = never
normal-∩ⁿˢ (R ⇒ S) (scalar T) = never
normal-∩ⁿˢ (R ⇒ S) error = never
normal-∩ⁿˢ (R ∩ S) (scalar T) = never
normal-∩ⁿˢ (R ∩ S) error = never
normal-∩ⁿˢ (R ∪ scalar S) (scalar T) with S ≡ˢ T
normal-∩ⁿˢ (R ∪ scalar S) (scalar T) | yes refl = scalar S
normal-∩ⁿˢ (R ∪ scalar S) (scalar T) | no p = normal-∩ⁿˢ R (scalar T)
normal-∩ⁿˢ (R ∪ error) error = error
normal-∩ⁿˢ (R ∪ error) (scalar T) = normal-∩ⁿˢ R (scalar T)
normal-∩ⁿˢ (R ∪ scalar S) error = normal-∩ⁿˢ R error

normal-∪ᶠ (R ⇒ S) (T ⇒ U) = (R ∩ T) ⇒ (S ∪ U)
normal-∪ᶠ (R ⇒ S) (G ∩ H) = normal-∪ᶠ (R ⇒ S) G ∩ normal-∪ᶠ (R ⇒ S) H
normal-∪ᶠ (E ∩ F) G = normal-∪ᶠ E G ∩ normal-∪ᶠ F G

fun-∩-scalar-<:-never : ∀ {F} → FunType F → ∀ S {V} → (F ∩ scalar S) <: V
fun-∩-scalar-<:-never (T ⇒ U) S = function-∩-scalar-<:-never S
fun-∩-scalar-<:-never (F ∩ G) S = <:-trans (<:-intersect <:-∩-left <:-refl) (fun-∩-scalar-<:-never F S)

fun-∩-error-<:-never : ∀ {F} → FunType F → ∀ {V} → (F ∩ error) <: V
fun-∩-error-<:-never (T ⇒ U) = function-∩-error-<:-never
fun-∩-error-<:-never (F ∩ G) = <:-trans (<:-intersect <:-∩-left <:-refl) (fun-∩-error-<:-never F)

flipper : ∀ {S T U} → ((S ∪ T) ∪ U) <: ((S ∪ U) ∪ T)
flipper = <:-trans <:-∪-assocr (<:-trans (<:-union <:-refl <:-∪-symm) <:-∪-assocl)

∩-<:-∩ⁿ :  ∀ {S T} → Normal S → Normal T → (S ∩ T) <: (S ∩ⁿ T)
∩ⁿ-<:-∩ :  ∀ {S T} → Normal S → Normal T → (S ∩ⁿ T) <: (S ∩ T)
∩-<:-∩ⁿˢ :  ∀ {S T} → Normal S → ErrScalar T → (S ∩ T) <: (S ∩ⁿˢ T)
∩ⁿˢ-<:-∩ :  ∀ {S T} → Normal S → ErrScalar T → (S ∩ⁿˢ T) <: (S ∩ T)
∪ᶠ-<:-∪ : ∀ {F G} → FunType F → FunType G → (F ∪ᶠ G) <: (F ∪ G)
∪ⁿ-<:-∪ : ∀ {S T} → Normal S → Normal T → (S ∪ⁿ T) <: (S ∪ T)
∪-<:-∪ⁿ : ∀ {S T} → Normal S → Normal T → (S ∪ T) <: (S ∪ⁿ T)
∪ⁿˢ-<:-∪ : ∀ {S T} → Normal S → OptScalar T → (S ∪ⁿˢ T) <: (S ∪ T)
∪-<:-∪ⁿˢ : ∀ {S T} → Normal S → OptScalar T → (S ∪ T) <: (S ∪ⁿˢ T)

∩-<:-∩ⁿ S never = <:-∩-right
∩-<:-∩ⁿ S (T ∪ U) = <:-trans <:-∩-distl-∪ (<:-trans (<:-union (∩-<:-∩ⁿ S T) (∩-<:-∩ⁿˢ S U)) (∪-<:-∪ⁿˢ (normal-∩ⁿ S T) (normal-∩ⁿˢ S U)) )
∩-<:-∩ⁿ never (T ⇒ U) = <:-∩-left
∩-<:-∩ⁿ (R ⇒ S) (T ⇒ U) = <:-refl
∩-<:-∩ⁿ (R ∩ S) (T ⇒ U) = <:-refl
∩-<:-∩ⁿ (R ∪ S) (T ⇒ U) = <:-trans <:-∩-distr-∪ (<:-trans (<:-union (∩-<:-∩ⁿ R (T ⇒ U)) (<:-trans <:-∩-symm (∩-<:-∩ⁿˢ (T ⇒ U) S))) (<:-∪-lub <:-refl <:-never))
∩-<:-∩ⁿ never (T ∩ U) = <:-∩-left
∩-<:-∩ⁿ (R ⇒ S) (T ∩ U) = <:-refl
∩-<:-∩ⁿ (R ∩ S) (T ∩ U) = <:-refl
∩-<:-∩ⁿ (R ∪ S) (T ∩ U) = <:-trans <:-∩-distr-∪ (<:-trans (<:-union (∩-<:-∩ⁿ R (T ∩ U)) (<:-trans <:-∩-symm (∩-<:-∩ⁿˢ (T ∩ U) S))) (<:-∪-lub <:-refl <:-never))

∩ⁿ-<:-∩ S never = <:-never
∩ⁿ-<:-∩ S (T ∪ U) = <:-trans (∪ⁿˢ-<:-∪ (normal-∩ⁿ S T) (normal-∩ⁿˢ S U)) (<:-trans (<:-union (∩ⁿ-<:-∩ S T) (∩ⁿˢ-<:-∩ S U)) ∩-distl-∪-<:)
∩ⁿ-<:-∩ never (T ⇒ U) = <:-never
∩ⁿ-<:-∩ (R ⇒ S) (T ⇒ U) = <:-refl
∩ⁿ-<:-∩ (R ∩ S) (T ⇒ U) = <:-refl
∩ⁿ-<:-∩ (R ∪ S) (T ⇒ U) = <:-trans (∩ⁿ-<:-∩ R (T ⇒ U)) (<:-∩-glb (<:-trans <:-∩-left <:-∪-left) <:-∩-right)
∩ⁿ-<:-∩ never (T ∩ U) = <:-never
∩ⁿ-<:-∩ (R ⇒ S) (T ∩ U) = <:-refl
∩ⁿ-<:-∩ (R ∩ S) (T ∩ U) = <:-refl
∩ⁿ-<:-∩ (R ∪ S) (T ∩ U) = <:-trans (∩ⁿ-<:-∩ R (T ∩ U)) (<:-∩-glb (<:-trans <:-∩-left <:-∪-left) <:-∩-right)

∩-<:-∩ⁿˢ never (scalar T) = <:-∩-left
∩-<:-∩ⁿˢ never error = <:-∩-left
∩-<:-∩ⁿˢ (R ⇒ S) error = function-∩-error-<:-never
∩-<:-∩ⁿˢ (R ⇒ S) (scalar T) = fun-∩-scalar-<:-never (R ⇒ S) T
∩-<:-∩ⁿˢ (F ∩ G) error = fun-∩-error-<:-never (F ∩ G)
∩-<:-∩ⁿˢ (F ∩ G) (scalar S) = fun-∩-scalar-<:-never (F ∩ G) S
∩-<:-∩ⁿˢ (R ∪ scalar S) (scalar T) with S ≡ˢ T
∩-<:-∩ⁿˢ (R ∪ scalar S) (scalar T) | yes refl = <:-∩-right
∩-<:-∩ⁿˢ (R ∪ scalar S) (scalar T) | no p = <:-trans <:-∩-distr-∪ (<:-∪-lub (∩-<:-∩ⁿˢ R (scalar T)) (scalar-≢-∩-<:-never S T p))
∩-<:-∩ⁿˢ (R ∪ error) error = <:-∩-right
∩-<:-∩ⁿˢ (R ∪ error) (scalar T) = <:-trans <:-∩-distr-∪ (<:-∪-lub (∩-<:-∩ⁿˢ R (scalar T)) (error-∩-scalar-<:-never T))
∩-<:-∩ⁿˢ (R ∪ scalar T) error = <:-trans <:-∩-distr-∪ (<:-∪-lub (∩-<:-∩ⁿˢ R error) (scalar-∩-error-<:-never T))

∩ⁿˢ-<:-∩ never T = <:-never
∩ⁿˢ-<:-∩ (R ⇒ S) T = <:-never
∩ⁿˢ-<:-∩ (F ∩ G) T = <:-never
∩ⁿˢ-<:-∩ (R ∪ scalar S) (scalar T) with S ≡ˢ T
∩ⁿˢ-<:-∩ (R ∪ scalar S) (scalar T) | yes refl = <:-∩-glb <:-∪-right <:-refl
∩ⁿˢ-<:-∩ (R ∪ scalar S) (scalar T) | no p = <:-trans (∩ⁿˢ-<:-∩ R (scalar T)) (<:-intersect <:-∪-left <:-refl)
∩ⁿˢ-<:-∩ (R ∪ scalar S) error = <:-trans (∩ⁿˢ-<:-∩ R error) (<:-intersect <:-∪-left <:-refl)
∩ⁿˢ-<:-∩ (R ∪ error) error = <:-∩-glb <:-∪-right <:-refl
∩ⁿˢ-<:-∩ (R ∪ error) (scalar S) = <:-trans (∩ⁿˢ-<:-∩ R (scalar S)) (<:-intersect <:-∪-left <:-refl)

∪ᶠ-<:-∪ (R ⇒ S) (T ⇒ U) = <:-function-∪-∩
∪ᶠ-<:-∪ (R ⇒ S) (G ∩ H) = <:-trans (<:-intersect (∪ᶠ-<:-∪ (R ⇒ S) G) (∪ᶠ-<:-∪ (R ⇒ S) H)) ∪-distl-∩-<:
∪ᶠ-<:-∪ (E ∩ F) G = <:-trans (<:-intersect (∪ᶠ-<:-∪ E G) (∪ᶠ-<:-∪ F G)) ∪-distr-∩-<:

∪-<:-∪ᶠ : ∀ {F G} → FunType F → FunType G → (F ∪ G) <: (F ∪ᶠ G)
∪-<:-∪ᶠ (R ⇒ S) (T ⇒ U) = <:-function-∪
∪-<:-∪ᶠ (R ⇒ S) (G ∩ H) = <:-trans <:-∪-distl-∩ (<:-intersect (∪-<:-∪ᶠ (R ⇒ S) G) (∪-<:-∪ᶠ (R ⇒ S) H))
∪-<:-∪ᶠ (E ∩ F) G = <:-trans <:-∪-distr-∩ (<:-intersect (∪-<:-∪ᶠ E G) (∪-<:-∪ᶠ F G))

∪ⁿˢ-<:-∪ S never = <:-∪-left
∪ⁿˢ-<:-∪ never (scalar T) = <:-refl
∪ⁿˢ-<:-∪ never error = <:-refl
∪ⁿˢ-<:-∪ (R ⇒ S) (scalar T) = <:-refl
∪ⁿˢ-<:-∪ (R ⇒ S) error = <:-refl
∪ⁿˢ-<:-∪ (R ∩ S) (scalar T) = <:-refl
∪ⁿˢ-<:-∪ (R ∩ S) error = <:-refl
∪ⁿˢ-<:-∪ (R ∪ scalar S) (scalar T) with S ≡ˢ T
∪ⁿˢ-<:-∪ (R ∪ scalar S) (scalar T) | yes refl = <:-∪-left
∪ⁿˢ-<:-∪ (R ∪ scalar S) (scalar T) | no p = <:-trans (<:-union (∪ⁿˢ-<:-∪ R (scalar T)) <:-refl) flipper
∪ⁿˢ-<:-∪ (R ∪ scalar S) error = <:-trans (<:-union (∪ⁿˢ-<:-∪ R error) <:-refl) flipper
∪ⁿˢ-<:-∪ (R ∪ error) (scalar T) = <:-trans (<:-union (∪ⁿˢ-<:-∪ R (scalar T)) <:-refl) flipper
∪ⁿˢ-<:-∪ (R ∪ error) error = <:-∪-left

∪-<:-∪ⁿˢ T never = <:-∪-lub <:-refl <:-never
∪-<:-∪ⁿˢ never (scalar T) = <:-refl
∪-<:-∪ⁿˢ never error = <:-refl
∪-<:-∪ⁿˢ (R ⇒ S) (scalar T) = <:-refl
∪-<:-∪ⁿˢ (R ⇒ S) error = <:-refl
∪-<:-∪ⁿˢ (R ∩ S) (scalar T) = <:-refl
∪-<:-∪ⁿˢ (R ∩ S) error = <:-refl
∪-<:-∪ⁿˢ (R ∪ scalar S) (scalar T) with S ≡ˢ T
∪-<:-∪ⁿˢ (R ∪ scalar S) (scalar T) | yes refl = <:-∪-lub <:-refl <:-∪-right
∪-<:-∪ⁿˢ (R ∪ scalar S) (scalar T) | no p = <:-trans flipper (<:-union (∪-<:-∪ⁿˢ R (scalar T)) <:-refl)
∪-<:-∪ⁿˢ (R ∪ scalar S) error = <:-trans flipper (<:-union (∪-<:-∪ⁿˢ R error) <:-refl)
∪-<:-∪ⁿˢ (R ∪ error) (scalar T) = <:-trans flipper (<:-union (∪-<:-∪ⁿˢ R (scalar T)) <:-refl)
∪-<:-∪ⁿˢ (R ∪ error) error = <:-∪-lub <:-refl <:-∪-right

∪ⁿ-<:-∪ S never = <:-∪-left
∪ⁿ-<:-∪ never (T ⇒ U) = <:-∪-right
∪ⁿ-<:-∪ (R ⇒ S) (T ⇒ U) = ∪ᶠ-<:-∪ (R ⇒ S) (T ⇒ U)
∪ⁿ-<:-∪ (R ∩ S) (T ⇒ U) = ∪ᶠ-<:-∪ (R ∩ S) (T ⇒ U)
∪ⁿ-<:-∪ (R ∪ S) (T ⇒ U) = <:-trans (<:-union (∪ⁿ-<:-∪ R (T ⇒ U)) <:-refl) (<:-∪-lub (<:-∪-lub (<:-trans <:-∪-left <:-∪-left) <:-∪-right) (<:-trans <:-∪-right <:-∪-left))
∪ⁿ-<:-∪ never (T ∩ U) = <:-∪-right
∪ⁿ-<:-∪ (R ⇒ S) (T ∩ U) = ∪ᶠ-<:-∪ (R ⇒ S) (T ∩ U)
∪ⁿ-<:-∪ (R ∩ S) (T ∩ U) = ∪ᶠ-<:-∪ (R ∩ S) (T ∩ U)
∪ⁿ-<:-∪ (R ∪ S) (T ∩ U) = <:-trans (<:-union (∪ⁿ-<:-∪ R (T ∩ U)) <:-refl) (<:-∪-lub (<:-∪-lub (<:-trans <:-∪-left <:-∪-left) <:-∪-right) (<:-trans <:-∪-right <:-∪-left))
∪ⁿ-<:-∪ S (T ∪ U) = <:-∪-lub (<:-trans (∪ⁿ-<:-∪ S T) (<:-union <:-refl <:-∪-left)) (<:-trans <:-∪-right <:-∪-right)

∪-<:-∪ⁿ S never = <:-∪-lub <:-refl <:-never
∪-<:-∪ⁿ never (T ⇒ U) = <:-∪-lub <:-never <:-refl
∪-<:-∪ⁿ (R ⇒ S) (T ⇒ U) = ∪-<:-∪ᶠ (R ⇒ S) (T ⇒ U)
∪-<:-∪ⁿ (R ∩ S) (T ⇒ U) = ∪-<:-∪ᶠ (R ∩ S) (T ⇒ U)
∪-<:-∪ⁿ (R ∪ S) (T ⇒ U) = <:-trans <:-∪-assocr (<:-trans (<:-union <:-refl <:-∪-symm) (<:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ R (T ⇒ U)) <:-refl)))
∪-<:-∪ⁿ never (T ∩ U) = <:-∪-lub <:-never <:-refl
∪-<:-∪ⁿ (R ⇒ S) (T ∩ U) = ∪-<:-∪ᶠ (R ⇒ S) (T ∩ U)
∪-<:-∪ⁿ (R ∩ S) (T ∩ U) = ∪-<:-∪ᶠ (R ∩ S) (T ∩ U)
∪-<:-∪ⁿ (R ∪ S) (T ∩ U) = <:-trans <:-∪-assocr (<:-trans (<:-union <:-refl <:-∪-symm) (<:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ R (T ∩ U)) <:-refl)))
∪-<:-∪ⁿ never (T ∪ U) = <:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ never T) <:-refl)
∪-<:-∪ⁿ (R ⇒ S) (T ∪ U) = <:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ (R ⇒ S) T) <:-refl)
∪-<:-∪ⁿ (R ∩ S) (T ∪ U) = <:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ (R ∩ S) T) <:-refl)
∪-<:-∪ⁿ (R ∪ S) (T ∪ U) = <:-trans <:-∪-assocl (<:-union (∪-<:-∪ⁿ (R ∪ S) T) <:-refl)

normalize-<: : ∀ T → normalize T <: T
<:-normalize : ∀ T → T <: normalize T

<:-normalize (scalar T) = <:-∪-right
<:-normalize error = <:-∪-right
<:-normalize (S ⇒ T) = <:-refl
<:-normalize never = <:-refl
<:-normalize any = <:-everything
<:-normalize (S ∪ T) = <:-trans (<:-union (<:-normalize S) (<:-normalize T)) (∪-<:-∪ⁿ (normal S) (normal T))
<:-normalize (S ∩ T) = <:-trans (<:-intersect (<:-normalize S) (<:-normalize T)) (∩-<:-∩ⁿ (normal S) (normal T))

normalize-<: (scalar T) = <:-∪-lub <:-never <:-refl
normalize-<: error = <:-∪-lub <:-never <:-refl
normalize-<: (S ⇒ T) = <:-refl
normalize-<: never = <:-refl
normalize-<: any = <:-any
normalize-<: (S ∪ T) = <:-trans (∪ⁿ-<:-∪ (normal S) (normal T)) (<:-union (normalize-<: S) (normalize-<: T))
normalize-<: (S ∩ T) = <:-trans (∩ⁿ-<:-∩ (normal S) (normal T)) (<:-intersect (normalize-<: S) (normalize-<: T))


