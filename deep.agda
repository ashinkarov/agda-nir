

infixr 5 _⇒_ 
data Ty : Set where
  ι : Ty
  _⇒_ : Ty → Ty → Ty

variable
  τ σ δ : Ty

infixl 5 _▹_
data Ctx : Set where
  ε : Ctx
  _▹_ : Ctx → Ty → Ctx

variable
  Γ Δ : Ctx

-- ε ▹ nat ▹ bool ▹ real
--     2     1      0
-- nat ∈ Γ
data _∈_ : Ty → Ctx → Set where
  here  : τ ∈ (Γ ▹ τ)
  there : τ ∈ Γ → τ ∈ (Γ ▹ σ)


-- Γ , (x : nat) ⊢ (x + 5) : nat
-- Γ             ⊢ λ x → x + 5 : nat ⇒ nat
data Lam : Ctx → Ty → Set where
  var : τ ∈ Γ → Lam Γ τ
  _$_ : Lam Γ (τ ⇒ σ) → Lam Γ τ → Lam Γ σ
  lam : Lam (Γ ▹ τ) σ → Lam Γ (τ ⇒ σ)


module Test where
  postulate
    nat real bool : Ty
    wk : Lam Γ τ → Lam (Γ ▹ σ) τ 

  C : Ctx
  C = ε ▹ nat ▹ real ▹ nat

  pf : nat ∈ C
  pf = there (there here)

  id : Lam Γ (τ ⇒ τ)
  id = lam (var here)

  k : Lam Γ (τ ⇒ σ ⇒ τ)
  k = lam (lam (var (there here)))


  foo : Lam Γ nat → Lam Γ nat
  foo e = lam (wk e) $ e
