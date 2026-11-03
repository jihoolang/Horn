{-# OPTIONS --safe --without-K #-}
------------------------------------------------------------------------
-- Checking implicational schematic certificates by evaluation.
--
-- Implication.agda proves each form that proves an implication sound in
-- any model of the rules: rule hypotheses, `apply`, induction with
-- generalized induction hypotheses, and `invert`. Here those forms get a
-- checking algorithm that Agda can run, with the checks of
-- src/schematic.rs, and a proof that whatever it accepts is valid in every
-- model:
--
--   accepts-sound : accepts goals code ≡ just tt → All (ValidGoal M) goals
--
-- The checker (module `Check`) depends on the signature, the rules and the
-- constructor lists only; the soundness proof (module `Sound`) takes the
-- model. So `refl : accepts goals code ≡ just tt` is checked once and then
-- gives the theorem in every model: derivability, or a structure such as
-- the integers.
--
-- Differences from the Rust checker, none of which lets more through than
-- the proved calculus allows:
--
-- * Hypotheses are kept as (step, hypothesis) pairs in step order, as Rust
--   keeps step indices; merging two lists keeps both entries of a step
--   unless they are equal.
-- * A case variable of an induction must not be generalized by an
--   induction hypothesis the case uses (Rust: the generalized variables
--   are the motive's, which the case variables are not).
-- * A rule whose conclusion has another head symbol than the inverted
--   hypothesis needs no case and no renaming; for another rule without a
--   case, the checker renames its variables apart itself and requires that
--   unification fail.
-- * Unification takes fuel (Unify.agda); running out rejects.
-- * Parsing, names and `def` are not modelled: the certificate arrives as
--   numbers (`Code`), terms as a table of trees.
------------------------------------------------------------------------
module ImplicationCheck where

open import Schematic
open import Implication
open import Unify
open Rule
open Σ
open RHyp

------------------------------------------------------------------------
-- Builtin arithmetic: Agda evaluates these in one step on numerals.

_<ᵇ_ : ℕ → ℕ → Bool
_     <ᵇ zero  = false
zero  <ᵇ suc _ = true
suc m <ᵇ suc n = m <ᵇ n
{-# BUILTIN NATLESS _<ᵇ_ #-}

_⊞_ : ℕ → ℕ → ℕ
zero  ⊞ n = n
suc m ⊞ n = suc (m ⊞ n)
{-# BUILTIN NATPLUS _⊞_ #-}

maxℕ : ℕ → ℕ → ℕ
maxℕ m n = if m <ᵇ n then n else m

maxL : List ℕ → ℕ
maxL []       = 0
maxL (x ∷ xs) = maxℕ x (maxL xs)

-- 0, 1, …, n - 1
upTo : ℕ → List ℕ
upTo n = go n []
  where
    go : ℕ → List ℕ → List ℕ
    go zero    acc = acc
    go (suc k) acc = go k (k ∷ acc)

------------------------------------------------------------------------
-- Decisions

_⊎?_ : {P Q : Set} → Dec P → Dec Q → Dec (P ⊎ Q)
yes p ⊎? _     = yes (inl p)
no _  ⊎? yes q = yes (inr q)
no n  ⊎? no m  = no (λ { (inl p) → n p ; (inr q) → m q })
infixr 1 _⊎?_

-- As Schematic's decisions, a `yes` keeps its proof unevaluated.
_≟ʰ_ : (a b : RHyp) → Dec (a ≡ b)
rhyp ps j g ≟ʰ rhyp qs k h with j ≟ₜ k
... | no n = no (λ { refl → n refl })
... | yes e₁ with ps ≟ₜs qs
...   | no n = no (λ { refl → n refl })
...   | yes e₂ with g ≟ℓ h
...     | no n  = no (λ { refl → n refl })
...     | yes e₃ = yes (cong₂ (λ a b → a b) (cong₂ rhyp e₂ e₁) e₃)

IsJust : {A : Set} → Maybe A → Set
IsJust {A} m = Σ A (λ a → m ≡ just a)

isJust? : {A : Set} (m : Maybe A) → Dec (IsJust m)
isJust? nothing  = no (λ { (_ , ()) })
isJust? (just a) = yes (a , refl)

-- Decisions that stop at the first witness. Schematic's `any?` decides
-- the head and the tail together, so it walks the whole list; here the
-- tail is an argument that evaluation forces only when the head fails.
orAny : {A : Set} {P : A → Set} {x : A} {xs : List A} → Dec (P x) → Dec (Any P xs) → Dec (Any P (x ∷ xs))
orAny (yes p) _      = yes (here p)
orAny (no n)  (yes a) = yes (there a)
orAny (no n)  (no m)  = no (λ { (here p) → n p ; (there a) → m a })

anyS? : {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Dec (Any P xs)
anyS? p? []       = no (λ ())
anyS? p? (x ∷ xs) = orAny (p? x) (anyS? p? xs)

andAll : {A : Set} {P : A → Set} {x : A} {xs : List A} → Dec (P x) → Dec (All P xs) → Dec (All P (x ∷ xs))
andAll (no n)  _      = no (λ { (p ∷ _) → n p })
andAll (yes p) (yes q) = yes (p ∷ q)
andAll (yes _) (no m)  = no (λ { (_ ∷ q) → m q })

allS? : {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (xs : List A) → Dec (All P xs)
allS? p? []       = yes []
allS? p? (x ∷ xs) = andAll (p? x) (allS? p? xs)

_∈S?_ : (x : ℕ) (xs : List ℕ) → Dec (x ∈ xs)
x ∈S? xs = anyS? (λ y → x ≟ y) xs

-- Whether every element of xs is in L, and in none of it. L is an
-- argument, so evaluation builds it once, and only as far as needed.
allIn? : (L xs : List ℕ) → Dec (All (λ x → x ∈ L) xs)
allIn? L xs = allS? (λ x → x ∈S? L) xs

noneIn? : (L xs : List ℕ) → Dec (All (λ x → ¬ (x ∈ L)) xs)
noneIn? L xs = allS? (λ x → not? (x ∈S? L)) xs

_∈ʰ?_ : (h : RHyp) (hs : List RHyp) → Dec (h ∈ hs)
h ∈ʰ? hs = anyS? (λ k → h ≟ʰ k) hs

------------------------------------------------------------------------
-- Hypotheses of a fact: (step, hypothesis), in step order.

Hyps : Set
Hyps = List (ℕ × RHyp)

rh : Hyps → List RHyp
rh = map snd

mutual
  merge : Hyps → Hyps → Hyps
  merge []       ys = ys
  merge (x ∷ xs) ys = merge₁ x xs ys

  merge₁ : ℕ × RHyp → Hyps → Hyps → Hyps
  merge₁ x xs []       = x ∷ xs
  merge₁ x xs (y ∷ ys) =
    if fst x <ᵇ fst y then x ∷ merge xs (y ∷ ys)
    else (if fst y <ᵇ fst x then y ∷ merge₁ x xs ys
          else pick ((fst x ≟ fst y) ×? (snd x ≟ʰ snd y)) (x ∷ merge xs ys) (x ∷ y ∷ merge xs ys))

mergeAll : List Hyps → Hyps
mergeAll []         = []
mergeAll (hs ∷ hss) = merge hs (mergeAll hss)

-- All variables of a hypothesis, and those it fixes (not generalized).
hypVars : RHyp → List ℕ
hypVars h = vars (rconcl h) ++ varss (rprem h)

fixedVars : RHyp → List ℕ
fixedVars h = without (hypVars h) (gen h)

fixedL : List RHyp → List ℕ
fixedL []       = []
fixedL (h ∷ hs) = fixedVars h ++ fixedL hs

allVarsL : List RHyp → List ℕ
allVarsL []       = []
allVarsL (h ∷ hs) = hypVars h ++ allVarsL hs

bvars : List (ℕ × Tm) → List ℕ
bvars []             = []
bvars ((_ , t) ∷ bs) = vars t ++ bvars bs

-- Bind each listed variable; an earlier binding of a variable wins.
substOf : List (ℕ × Tm) → Subst
substOf []             x = var x
substOf ((y , t) ∷ bs) x = pick (y ≟ x) t (substOf bs x)

------------------------------------------------------------------------
-- The certificate

data Ref : Set where
  ref : ℕ → Ref
  inR : ℕ → List (ℕ × Tm) → Ref

data Form : Set where
  -- (hyp N (P...) J (X...)); a plain hypothesis has no P and no X
  hypF    : List Tm → Tm → List ℕ → Form
  -- (step N RULE (REF...) ITEM...): rule index, references, bindings,
  -- the stated conclusion
  ruleF   : ℕ → List Ref → List (ℕ × Tm) → Maybe Tm → Form
  -- (apply N M (BIND...) (REF...))
  applyF  : ℕ → List (ℕ × Tm) → List Ref → Form
  -- (induct N X (H...) J (CASE...)): per constructor of X's sort, the
  -- case step and its variables
  inductF : ℕ → List ℕ → Tm → List (ℕ × List ℕ) → Form
  -- (invert N K (C...) J (CASE...)): per rule given a case, the rule's
  -- index, the case step and the rule's variables renamed
  invertF : ℕ → List ℕ → Tm → List (ℕ × (ℕ × List ℕ)) → Form

-- Renaming a rule's variables apart, for inversion.

ruleVars : Rule → List ℕ
ruleVars r = varss (prem r) ++ vars (concl r)

usedVars : Tm → Tm → List RHyp → List ℕ
usedVars h J C = vars h ++ (vars J ++ allVarsL C)

-- Rule variable y is renamed to the y-th of xs.
renF : List ℕ → ℕ → ℕ
renF xs y = nth xs y 0

renS : List ℕ → Subst
renS xs y = var (renF xs y)

indexOf : ℕ → List ℕ → Maybe ℕ
indexOf x []       = nothing
indexOf x (y ∷ ys) = pick (x ≟ y) (just 0) (indexOf x ys >>= λ i → just (suc i))

backF : Rule → List ℕ → ℕ → Maybe ℕ
backF r xs x = indexOf x xs >>= λ i → when (i ∈? ruleVars r) i

-- A goal: hypotheses and judgment.
Goal : Set
Goal = List Tm × Tm

------------------------------------------------------------------------
-- Theories as tables, as Schematic's `Tables`, with the sorts of the
-- variables in a Braun tree: a certificate declares thousands of variables,
-- and a lookup in a list would cost up to their number.

allT? : {A : Set} {P : A → Set} → (∀ x → Dec (P x)) → (t : Tree A) → Dec (AllT P t)
allT? p? leaf        = yes leaf
allT? p? (bin x l r) with p? x | allT? p? l | allT? p? r
... | yes px | yes pl | yes pr = yes (bin px pl pr)
... | no n   | _      | _      = no (λ { (bin px _ _) → n px })
... | yes _  | no n   | _      = no (λ { (bin _ pl _) → n pl })
... | yes _  | yes _  | no n   = no (λ { (bin _ _ pr) → n pr })

module TreeTables (outT : List ℕ) (insT : List (List ℕ)) (varT : Tree ℕ) (junk : ℕ)
                  (rules : List Rule) where
  sortOf : Maybe ℕ → ℕ
  sortOf nothing  = 0
  sortOf (just s) = s

  sig : Signature
  sig = record { out = λ c → nth outT c junk ; ins = λ c → nth insT c [] ; vs = λ x → sortOf (lookupT varT x) }

  open Signature sig public
  open Calculus sig rules public

  ctors : ℕ → List ℕ
  ctors s = indicesOf 0 outT s

  NoJunk : Set
  NoJunk = (¬ (0 ≡ junk)) × AllT (λ s → ¬ (s ≡ junk)) varT

  junk? : Dec NoJunk
  junk? = not? (0 ≟ junk) ×? allT? (λ s → not? (s ≟ junk)) varT

  -- Complete for every variable's sort, provided `junk` is not one.
  complete-from : NoJunk → (c x : ℕ) → out c ≡ vs x → c ∈ ctors (vs x)
  complete-from (z , nj) c x e = indicesOf-∈ junk (vs x) 0 outT c e not-junk
    where
      not-junk : ¬ (vs x ≡ junk)
      not-junk with lookupT varT x in eq
      ... | nothing = z
      ... | just s  = allT-lookup nj x eq

------------------------------------------------------------------------
-- The checker

module Check (Sg : Signature) (R : List Rule) (ctors : ℕ → List ℕ) where
  open Signature Sg
  open Rules Sg R
  open Matching Sg R

  data Fact : Set where
    -- a judgment under hypotheses
    fact : Hyps → Tm → Fact
    -- step n assumes h
    hypo : ℕ → RHyp → Fact

  Facts : Set
  Facts = Tree Fact

  Plain : RHyp → Set
  Plain h = (rprem h ≡ []) × (gen h ≡ [])

  plain? : (h : RHyp) → Dec (Plain h)
  plain? h = (rprem h ≟ₜs []) ×? (gen h ≟ℓ [])

  bindsWS? : (bs : List (ℕ × Tm)) → Dec (All (λ b → WS (snd b) (vs (fst b))) bs)
  bindsWS? = all? (λ b → ws? (snd b) (vs (fst b)))

  -- A fact as a premise. A rule hypothesis is used only by `apply`.
  asPremise : Fact → Maybe (Hyps × Tm)
  asPremise (fact hs j) = just (hs , j)
  asPremise (hypo n h)  = when (plain? h) (((n , h) ∷ []) , rconcl h)

  -- Only hypothesis-free facts are instantiated.
  instFact : List (ℕ × Tm) → Fact → Maybe (Hyps × Tm)
  instFact bs (fact []      j) = when (bindsWS? bs) ([] , sub (substOf bs) j)
  instFact bs (fact (_ ∷ _) j) = nothing
  instFact bs (hypo _ _)       = nothing

  resolve : Facts → Ref → Maybe (Hyps × Tm)
  resolve fs (ref n)   = lookupT fs n >>= asPremise
  resolve fs (inR n bs) = lookupT fs n >>= instFact bs

  resolveAll : Facts → List Ref → Maybe (List (Hyps × Tm))
  resolveAll fs []       = just []
  resolveAll fs (r ∷ rs) = resolve fs r >>= λ q → resolveAll fs rs >>= λ qs → just (q ∷ qs)

  -- The premises' hypotheses: concatenated (as the calculus has them) and
  -- merged (as the fact keeps them).
  allHyps : List (Hyps × Tm) → List RHyp
  allHyps []       = []
  allHyps (q ∷ qs) = rh (fst q) ++ allHyps qs

  joined : List (Hyps × Tm) → Hyps
  joined qs = mergeAll (map fst qs)

  -- (hyp N (P...) J (X...))
  checkHyp : ℕ → List Tm → Tm → List ℕ → Maybe Fact
  checkHyp n ps j g = when (ws? j (headSort j)) (hypo n (rhyp ps j g))

  -- A rule step, as in Schematic.agda's algorithm; the variables of a
  -- premise must occur in the conclusion or be fixed by a hypothesis.
  checkRule : Facts → ℕ → List Ref → List (ℕ × Tm) → Maybe Tm → Maybe Fact
  checkRule fs n refs binds stated =
    lookup R n >>= λ r →
    resolveAll fs refs >>= λ qs →
    bindAll r binds empty >>= λ b₀ →
    conclude (concl r) stated b₀ >>= λ b₁ →
    matchs (prem r) (map snd qs) b₁ >>= λ b₂ →
    answer stated (instE b₂ (concl r)) >>= λ J →
    when (all? (λ y → ws? (total b₂ y) (rs r y)) (conclOnly r)) tt >>= λ _ →
    when (allIn? (vars J ++ fixedL (allHyps qs)) (concatMap (λ y → vars (total b₂ y)) (premOnly r)))
         (fact (joined qs) J)

  -- The variables an instantiated premise or a binding brings in must
  -- occur in the conclusion or be fixed by a hypothesis.
  SideOk : Tm → List RHyp → List (ℕ × Tm) → List Tm → Set
  SideOk J H bs ps = All (λ x → x ∈ (vars J ++ fixedL H)) (varss ps ++ bvars bs)

  sideOk? : (J : Tm) (H : List RHyp) (bs : List (ℕ × Tm)) (ps : List Tm) → Dec (SideOk J H bs ps)
  sideOk? J H bs ps = allIn? (vars J ++ fixedL H) (varss ps ++ bvars bs)

  -- (apply N M BIND REF...) with M a hypothesis h: the bindings
  -- instantiate only h's generalized variables.
  applyHyp : ℕ → RHyp → List (ℕ × Tm) → List (Hyps × Tm) → Maybe Fact
  applyHyp i h bs qs =
    when (all? (λ b → fst b ∈? gen h) bs) tt >>= λ _ →
    when (map snd qs ≟ₜs map (sub (substOf bs)) (rprem h)) tt >>= λ _ →
    when (sideOk? (sub (substOf bs) (rconcl h)) (h ∷ allHyps qs) bs (map snd qs))
         (fact (merge ((i , h) ∷ []) (joined qs)) (sub (substOf bs) (rconcl h)))

  -- Judgments of plain hypotheses.
  plains : List RHyp → Maybe (List Tm)
  plains []       = just []
  plains (h ∷ hs) = when (plain? h) (rconcl h) >>= λ p → plains hs >>= λ ps → just (p ∷ ps)

  -- (apply N M BIND REF...) with M an implication proved earlier, whose
  -- hypotheses are plain: they are its premises, in step order.
  applyFact : Hyps → Tm → List (ℕ × Tm) → List (Hyps × Tm) → Maybe Fact
  applyFact hs J bs qs =
    plains (rh hs) >>= λ Ps →
    when (map snd qs ≟ₜs map (sub (substOf bs)) Ps) tt >>= λ _ →
    when (sideOk? (sub (substOf bs) J) (allHyps qs) bs (map snd qs))
         (fact (joined qs) (sub (substOf bs) J))

  applyTo : Fact → List (ℕ × Tm) → List (Hyps × Tm) → Maybe Fact
  applyTo (hypo i h)  = applyHyp i h
  applyTo (fact hs J) = applyFact hs J

  checkApply : Facts → ℕ → List (ℕ × Tm) → List Ref → Maybe Fact
  checkApply fs m bs refs =
    when (bindsWS? bs) tt >>= λ _ →
    lookupT fs m >>= λ f → resolveAll fs refs >>= applyTo f bs

  -- A plain hypothesis: its step and judgment.
  plainHyp : Fact → Maybe (ℕ × Tm)
  plainHyp (hypo n h)  = when (plain? h) (n , rconcl h)
  plainHyp (fact _ _)  = nothing

  plainHyps : Facts → List ℕ → Maybe (List (ℕ × Tm))
  plainHyps fs []       = just []
  plainHyps fs (i ∷ is) =
    lookupT fs i >>= plainHyp >>= λ p → plainHyps fs is >>= λ ps → just (p ∷ ps)

  asHyps : List (ℕ × Tm) → Hyps
  asHyps = map (λ p → fst p , plainR (snd p))

  -- What a case of an induction on X (hypotheses Ps, motive J) for
  -- constructor c with variables ys may assume: a premise at c(ys), or the
  -- induction hypothesis at some y of X's sort, generalizing no case
  -- variable.
  IHAt : ℕ → List Tm → Tm → List ℕ → RHyp → Set
  IHAt X Ps J ys h =
    Any (λ y → (vs y ≡ vs X) × (h ≡ rhyp (map (sub (point X (var y))) Ps) (sub (point X (var y)) J) (gen h))) ys
    × All (λ g → ¬ (g ∈ ys)) (gen h)

  CaseH : ℕ → List Tm → Tm → ℕ → List ℕ → RHyp → Set
  CaseH X Ps J c ys h =
    (h ∈ map (λ p → plainR (sub (point X (node c (map var ys))) p)) Ps) ⊎ IHAt X Ps J ys h

  caseH? : (X : ℕ) (Ps : List Tm) (J : Tm) (c : ℕ) (ys : List ℕ) (h : RHyp) → Dec (CaseH X Ps J c ys h)
  caseH? X Ps J c ys h =
    (h ∈ʰ? map (λ p → plainR (sub (point X (node c (map var ys))) p)) Ps)
    ⊎? (any? (λ y → (vs y ≟ vs X) ×? (h ≟ʰ rhyp (map (sub (point X (var y))) Ps) (sub (point X (var y)) J) (gen h))) ys
        ×? all? (λ g → not? (g ∈? ys)) (gen h))

  CaseOk : ℕ → List Tm → Tm → ℕ → List ℕ → Hyps → Tm → Set
  CaseOk X Ps J c ys hs Jm =
    (map vs ys ≡ ins c) × Distinct ys × All (λ y → ¬ (y ∈ (vars J ++ varss Ps))) ys
    × (Jm ≡ sub (point X (node c (map var ys))) J) × All (CaseH X Ps J c ys) (rh hs)

  caseOk? : (X : ℕ) (Ps : List Tm) (J : Tm) (c : ℕ) (ys : List ℕ) (hs : Hyps) (Jm : Tm)
          → Dec (CaseOk X Ps J c ys hs Jm)
  caseOk? X Ps J c ys hs Jm =
    (map vs ys ≟ℓ ins c) ×? distinct? ys ×? noneIn? (vars J ++ varss Ps) ys
    ×? (Jm ≟ₜ sub (point X (node c (map var ys))) J) ×? all? (caseH? X Ps J c ys) (rh hs)

  checkCases : Facts → ℕ → List Tm → Tm → List ℕ → List (ℕ × List ℕ) → Maybe ⊤
  checkCases fs X Ps J []       []              = just tt
  checkCases fs X Ps J (c ∷ cs) ((m , ys) ∷ ks) =
    lookupT fs m >>= asPremise >>= λ q →
    when (caseOk? X Ps J c ys (fst q) (snd q)) tt >>= λ _ → checkCases fs X Ps J cs ks
  checkCases fs X Ps J []       (k ∷ ks)        = nothing
  checkCases fs X Ps J (c ∷ cs) []              = nothing

  -- (induct N X (H...) J (CASE...)), the H plain hypotheses
  checkInduct : Facts → ℕ → List ℕ → Tm → List (ℕ × List ℕ) → Maybe Fact
  checkInduct fs X is J ks =
    plainHyps fs is >>= λ ps →
    when (ws? J (headSort J)) tt >>= λ _ →
    when (X ∈? (vars J ++ varss (map snd ps))) tt >>= λ _ →
    checkCases fs X (map snd ps) J (ctors (vs X)) ks >>= λ _ →
    just (fact (asHyps ps) J)

  ----------------------------------------------------------------------
  -- Inversion

  -- Hypotheses of any kind.
  anyHyp : Fact → Maybe (ℕ × RHyp)
  anyHyp (hypo n h)  = just (n , h)
  anyHyp (fact _ _)  = nothing

  ctxHyps : Facts → List ℕ → Maybe Hyps
  ctxHyps fs []       = just []
  ctxHyps fs (i ∷ is) = lookupT fs i >>= anyHyp >>= λ p → ctxHyps fs is >>= λ ps → just (p ∷ ps)

  -- The renaming is injective, defined on the rule's variables, and fresh.
  RenOk : Rule → List ℕ → List ℕ → Set
  RenOk r xs used =
    Distinct xs × All (λ y → IsJust (lookup xs y)) (ruleVars r) × All (λ x → ¬ (x ∈ used)) xs

  renOk? : (r : Rule) (xs used : List ℕ) → Dec (RenOk r xs used)
  renOk? r xs used =
    distinct? xs ×? all? (λ y → isJust? (lookup xs y)) (ruleVars r) ×? noneIn? used xs

  Sorted : Rule → List ℕ → Set
  Sorted r xs = All (λ y → vs (renF xs y) ≡ rs r y) (ruleVars r)

  sorted? : (r : Rule) (xs : List ℕ) → Dec (Sorted r xs)
  sorted? r xs = all? (λ y → vs (renF xs y) ≟ rs r y) (ruleVars r)

  -- Fresh variables for a rule given no case.
  freshFor : List ℕ → Rule → List ℕ
  freshFor used r = map (λ i → suc (maxL used) ⊞ i) (upTo (suc (maxL (ruleVars r))))

  fuel : ℕ
  fuel = 1000000

  okOf : Outcome → Maybe Subst
  okOf (ok θ) = just θ
  okOf none   = nothing
  okOf stuck  = nothing

  IsNone : Outcome → Set
  IsNone o = o ≡ none

  isNone? : (o : Outcome) → Dec (IsNone o)
  isNone? (ok θ) = no (λ ())
  isNone? none   = yes refl
  isNone? stuck  = no (λ ())

  -- θ does not capture a generalized variable of a context hypothesis.
  NoCap : List RHyp → Subst → Set
  NoCap C θ = All (λ c → All (λ x → All (λ g → ¬ (g ∈ vars (θ x))) (gen c)) (fixedVars c)) C

  noCap? : (C : List RHyp) (θ : Subst) → Dec (NoCap C θ)
  noCap? C θ = all? (λ c → all? (λ x → all? (λ g → not? (g ∈? vars (θ x))) (gen c)) (fixedVars c)) C

  allowedInv : Subst → List ℕ → Rule → List RHyp → List RHyp
  allowedInv θ xs r C = map (λ p → plainR (sub θ (sub (renS xs) p))) (prem r) ++ map (appθ θ) C

  invCase : Facts → Tm → Tm → List RHyp → Rule → List ℕ → ℕ → Maybe ⊤
  invCase fs h J C r xs m =
    when (renOk? r xs (usedVars h J C)) tt >>= λ _ →
    when (sorted? r xs) tt >>= λ _ →
    when (ws? (sub (renS xs) (concl r)) (headSort h)) tt >>= λ _ →
    okOf (mgu fuel h (sub (renS xs) (concl r))) >>= λ θ →
    when (noCap? C θ) tt >>= λ _ →
    lookupT fs m >>= asPremise >>= λ q →
    when (snd q ≟ₜ sub θ J) tt >>= λ _ →
    when (all? (λ k → k ∈ʰ? allowedInv θ xs r C) (rh (fst q))) tt

  noCase : Tm → Tm → List RHyp → Rule → Maybe ⊤
  noCase h J C r =
    when (renOk? r (freshFor (usedVars h J C) r) (usedVars h J C)) tt >>= λ _ →
    when (isNone? (mgu fuel h (sub (renS (freshFor (usedVars h J C) r)) (concl r)))) tt

  Clash : Tm → Tm → Set
  Clash h c = Σ ℕ (λ f → Σ (List Tm) (λ ts → Σ ℕ (λ g → Σ (List Tm) (λ us →
                (h ≡ node f ts) × (c ≡ node g us) × ¬ (f ≡ g)))))

  clash? : (h c : Tm) → Dec (Clash h c)
  clash? (node f ts) (node g us) with f ≟ g
  ... | yes e = no (λ { (_ , _ , _ , _ , refl , refl , ne) → ne e })
  ... | no ne = yes (f , ts , g , us , refl , refl , ne)
  clash? (var x)     c           = no (λ { (_ , _ , _ , _ , () , _) })
  clash? (node f ts) (var y)     = no (λ { (_ , _ , _ , _ , _ , () , _) })

  findCase : ℕ → List (ℕ × (ℕ × List ℕ)) → Maybe (ℕ × List ℕ)
  findCase i []             = nothing
  findCase i ((j , c) ∷ ks) = pick (i ≟ j) (just c) (findCase i ks)

  ruleCase : Facts → Tm → Tm → List RHyp → List (ℕ × (ℕ × List ℕ)) → ℕ → Rule → Maybe ⊤
  ruleCase fs h J C ks i r with clash? h (concl r)
  ... | yes _ = just tt
  ... | no _ with findCase i ks
  ...   | just (m , xs) = invCase fs h J C r xs m
  ...   | nothing       = noCase h J C r

  allRules : Facts → Tm → Tm → List RHyp → List (ℕ × (ℕ × List ℕ)) → ℕ → List Rule → Maybe ⊤
  allRules fs h J C ks i []       = just tt
  allRules fs h J C ks i (r ∷ rs) = ruleCase fs h J C ks i r >>= λ _ → allRules fs h J C ks (suc i) rs

  -- (invert N K (C...) J (CASE...)), K a plain hypothesis
  checkInvert : Facts → ℕ → List ℕ → Tm → List (ℕ × (ℕ × List ℕ)) → Maybe Fact
  checkInvert fs k is J ks =
    lookupT fs k >>= plainHyp >>= λ kh →
    ctxHyps fs is >>= λ C →
    when (ws? J (headSort J)) tt >>= λ _ →
    allRules fs (snd kh) J (rh C) ks 0 R >>= λ _ →
    just (fact (merge C ((fst kh , plainR (snd kh)) ∷ [])) J)

  ----------------------------------------------------------------------
  -- Steps, goals and the certificate as numbers

  checkStep : Facts → ℕ → Form → Maybe Fact
  checkStep fs n (hypF ps j g)              = checkHyp n ps j g
  checkStep fs n (ruleF r refs binds stated) = checkRule fs r refs binds stated
  checkStep fs n (applyF m bs refs)         = checkApply fs m bs refs
  checkStep fs n (inductF X is J ks)        = checkInduct fs X is J ks
  checkStep fs n (invertF k is J ks)        = checkInvert fs k is J ks

  -- The result may use only plain hypotheses the goal states.
  GoalOk : Hyps → Tm → Goal → Set
  GoalOk hs J g = (J ≡ snd g) × All (λ h → h ∈ map plainR (fst g)) (rh hs)

  goalOk? : (hs : Hyps) (J : Tm) (g : Goal) → Dec (GoalOk hs J g)
  goalOk? hs J g = (J ≟ₜ snd g) ×? all? (λ h → h ∈ʰ? map plainR (fst g)) (rh hs)

  --   CODE  = N ENTRY^N  M FORM^M  REF^(goals)
  --   ENTRY = 0 x | 1 f k TERM^k        (TERM: index of an earlier entry)
  --   FORM  = 0 k TERM^k TERM g x^g                   hyp
  --         | 1 r n REF^n b (y TERM)^b STATED         step
  --         | 2 M b (x TERM)^b n REF^n                apply
  --         | 3 X h H^h TERM k CASE^k                 induct; CASE = m k y^k
  --         | 4 K c C^c TERM k ICASE^k                invert; ICASE = r m k x^k
  --   REF   = 0 n | 1 n b (x TERM)^b ;  STATED = 0 | 1 TERM

  Parser : Set → Set
  Parser A = Code → Maybe (A × Code)

  pureₚ : {A : Set} → A → Parser A
  pureₚ a c = just (a , c)

  _>>=ₚ_ : {A B : Set} → Parser A → (A → Parser B) → Parser B
  (p >>=ₚ f) c = p c >>= λ r → f (fst r) (snd r)
  infixl 1 _>>=ₚ_

  liftₚ : {A : Set} → Maybe A → Parser A
  liftₚ nothing  c = nothing
  liftₚ (just a) c = just (a , c)

  num : Parser ℕ
  num ε                  = nothing
  num (n ▸ c)            = just (n , c)
  num (pack zero w c)    = num c
  num (pack (suc k) w c) =
    just (mod-helper 0 4294967295 w 4294967295 , pack k (div-helper 0 4294967295 w 4294967295) c)

  many : {A : Set} → ℕ → Parser A → Parser (List A)
  many zero    p = pureₚ []
  many (suc k) p = p >>=ₚ λ a → many k p >>=ₚ λ as → pureₚ (a ∷ as)

  listP : {A : Set} → Parser A → Parser (List A)
  listP p = num >>=ₚ λ k → many k p

  TmTable : Set
  TmTable = Tree Tm

  tmP : TmTable → Parser Tm
  tmP T = num >>=ₚ λ i → liftₚ (lookupT T i)

  entryP : TmTable → ℕ → Parser Tm
  entryP T zero    = num >>=ₚ λ x → pureₚ (var x)
  entryP T (suc _) = num >>=ₚ λ f → listP (tmP T) >>=ₚ λ ts → pureₚ (node f ts)

  table : ℕ → ℕ → TmTable → Parser TmTable
  table zero    i T = pureₚ T
  table (suc n) i T = num >>=ₚ entryP T >>=ₚ λ t → table n (suc i) (insertT T i t)

  binding : TmTable → Parser (ℕ × Tm)
  binding T = num >>=ₚ λ x → tmP T >>=ₚ λ t → pureₚ (x , t)

  refTag : TmTable → ℕ → Parser Ref
  refTag T zero    = num >>=ₚ λ n → pureₚ (ref n)
  refTag T (suc _) = num >>=ₚ λ n → listP (binding T) >>=ₚ λ bs → pureₚ (inR n bs)

  refP : TmTable → Parser Ref
  refP T = num >>=ₚ refTag T

  statedTag : TmTable → ℕ → Parser (Maybe Tm)
  statedTag T zero    = pureₚ nothing
  statedTag T (suc _) = tmP T >>=ₚ λ j → pureₚ (just j)

  caseP : Parser (ℕ × List ℕ)
  caseP = num >>=ₚ λ m → listP num >>=ₚ λ ys → pureₚ (m , ys)

  icaseP : Parser (ℕ × (ℕ × List ℕ))
  icaseP = num >>=ₚ λ r → num >>=ₚ λ m → listP num >>=ₚ λ xs → pureₚ (r , (m , xs))

  formTag : TmTable → ℕ → Parser Form
  formTag T zero =
    listP (tmP T) >>=ₚ λ ps → tmP T >>=ₚ λ j → listP num >>=ₚ λ g → pureₚ (hypF ps j g)
  formTag T (suc zero) =
    num >>=ₚ λ r → listP (refP T) >>=ₚ λ refs → listP (binding T) >>=ₚ λ bs →
    num >>=ₚ statedTag T >>=ₚ λ st → pureₚ (ruleF r refs bs st)
  formTag T (suc (suc zero)) =
    num >>=ₚ λ m → listP (binding T) >>=ₚ λ bs → listP (refP T) >>=ₚ λ refs → pureₚ (applyF m bs refs)
  formTag T (suc (suc (suc zero))) =
    num >>=ₚ λ X → listP num >>=ₚ λ is → tmP T >>=ₚ λ J → listP caseP >>=ₚ λ ks → pureₚ (inductF X is J ks)
  formTag T (suc (suc (suc (suc _)))) =
    num >>=ₚ λ k → listP num >>=ₚ λ is → tmP T >>=ₚ λ J → listP icaseP >>=ₚ λ ks → pureₚ (invertF k is J ks)

  formP : TmTable → Parser Form
  formP T = num >>=ₚ formTag T

  -- Steps are decoded and checked one at a time.
  checkStream : TmTable → Facts → ℕ → ℕ → Code → Maybe (Facts × Code)
  checkStream T fs n zero    c = just (fs , c)
  checkStream T fs n (suc k) c =
    formP T c >>= λ r → checkStep fs n (fst r) >>= λ f → checkStream T (insertT fs n f) (suc n) k (snd r)

  checkGoals : TmTable → Facts → List Goal → Code → Maybe ⊤
  checkGoals T fs []       c = just tt
  checkGoals T fs (g ∷ gs) c =
    refP T c >>= λ r → resolve fs (fst r) >>= λ q →
    when (goalOk? (fst q) (snd q) g) tt >>= λ _ → checkGoals T fs gs (snd r)

  accepts : List Goal → Code → Maybe ⊤
  accepts goals c =
    num c >>= λ r₁ → table (fst r₁) 0 leaf (snd r₁) >>= λ r₂ →
    num (snd r₂) >>= λ r₃ → checkStream (fst r₂) leaf 0 (fst r₃) (snd r₃) >>= λ r₄ →
    checkGoals (fst r₂) (fst r₄) goals (snd r₄)

------------------------------------------------------------------------
-- Lemmas on lists, hypothesis lists and substitutions

pair≡ : {A B : Set} {a b : A × B} → fst a ≡ fst b → snd a ≡ snd b → a ≡ b
pair≡ {a = a₁ , a₂} {b = b₁ , b₂} refl refl = refl

∈-map⁺ : {A B : Set} (f : A → B) {x : A} {xs : List A} → x ∈ xs → f x ∈ map f xs
∈-map⁺ f (here refl) = here refl
∈-map⁺ f (there m)   = there (∈-map⁺ f m)

∈-map⁻ : {A B : Set} (f : A → B) (xs : List A) {y : B} → y ∈ map f xs → Σ A (λ x → (x ∈ xs) × (y ≡ f x))
∈-map⁻ f (x ∷ xs) (here e)  = x , here refl , e
∈-map⁻ f (x ∷ xs) (there m) with ∈-map⁻ f xs m
... | z , mz , e = z , there mz , e

mutual
  merge-l : {p : ℕ × RHyp} (xs ys : Hyps) → p ∈ xs → p ∈ merge xs ys
  merge-l (x ∷ xs) ys m = merge₁-l x xs ys m

  merge-r : {p : ℕ × RHyp} (xs ys : Hyps) → p ∈ ys → p ∈ merge xs ys
  merge-r []       ys m = m
  merge-r (x ∷ xs) ys m = merge₁-r x xs ys m

  merge₁-l : {p : ℕ × RHyp} (x : ℕ × RHyp) (xs ys : Hyps) → p ∈ (x ∷ xs) → p ∈ merge₁ x xs ys
  merge₁-l x xs []       m = m
  merge₁-l x xs (y ∷ ys) m with fst x <ᵇ fst y
  ... | true = cons m
    where
      cons : _ → _
      cons (here e)  = here e
      cons (there m′) = there (merge-l xs (y ∷ ys) m′)
  ... | false with fst y <ᵇ fst x
  ...   | true = there (merge₁-l x xs ys m)
  ...   | false with (fst x ≟ fst y) ×? (snd x ≟ʰ snd y)
  ...     | yes _ = cons m
    where
      cons : _ → _
      cons (here e)   = here e
      cons (there m′) = there (merge-l xs ys m′)
  ...     | no _ = cons m
    where
      cons : _ → _
      cons (here e)   = here e
      cons (there m′) = there (there (merge-l xs ys m′))

  merge₁-r : {p : ℕ × RHyp} (x : ℕ × RHyp) (xs ys : Hyps) → p ∈ ys → p ∈ merge₁ x xs ys
  merge₁-r x xs (y ∷ ys) m with fst x <ᵇ fst y
  ... | true = there (merge-r xs (y ∷ ys) m)
  ... | false with fst y <ᵇ fst x
  ...   | true = cons m
    where
      cons : _ → _
      cons (here e)   = here e
      cons (there m′) = there (merge₁-r x xs ys m′)
  ...   | false with (fst x ≟ fst y) ×? (snd x ≟ʰ snd y)
  ...     | yes (e₁ , e₂) = cons m
    where
      cons : _ → _
      cons (here e)   = here (trans e (pair≡ (sym e₁) (sym e₂)))
      cons (there m′) = there (merge-r xs ys m′)
  ...     | no _ = cons m
    where
      cons : _ → _
      cons (here e)   = there (here e)
      cons (there m′) = there (there (merge-r xs ys m′))

-- Inclusion of hypothesis lists, through `rh`.
rh-⊆ : {A B : Hyps} → (∀ {p} → p ∈ A → p ∈ B) → ∀ {h} → h ∈ rh A → h ∈ rh B
rh-⊆ {A} inc m with ∈-map⁻ snd A m
... | p , mp , refl = ∈-map⁺ snd (inc mp)

without-∉ : {x : ℕ} (xs ys : List ℕ) → x ∈ without xs ys → ¬ (x ∈ ys)
without-∉ (z ∷ xs) ys m with z ∈? ys
... | yes _ = without-∉ xs ys m
without-∉ (z ∷ xs) ys (here refl) | no n = n
without-∉ (z ∷ xs) ys (there m)   | no _ = without-∉ xs ys m

lookup-nth : {A : Set} (xs : List A) (i : ℕ) (d : A) {a : A} → lookup xs i ≡ just a → nth xs i d ≡ a
lookup-nth (x ∷ xs) zero    d refl = refl
lookup-nth (x ∷ xs) (suc i) d e    = lookup-nth xs i d e
lookup-nth []       i       d ()

subs-map : (σ : Subst) (ts : List Tm) → subs σ ts ≡ map (sub σ) ts
subs-map σ []       = refl
subs-map σ (t ∷ ts) = cong (sub σ t ∷_) (subs-map σ ts)

-- An instance keeps a variable that the substitution leaves alone.
occ-keep : (σ : Subst) (t : Tm) {y : ℕ} → σ y ≡ var y → Occ y t → Occ y (sub σ t)
occ-keep σ t {y} e o = sub-occ σ t o (transport (Occ y) (sym e) here)

occs-keep : (σ : Subst) (ts : List Tm) {y : ℕ} → σ y ≡ var y → Occs y ts → Occs y (subs σ ts)
occs-keep σ ts {y} e o = subs-occ σ ts o (transport (Occ y) (sym e) here)

bvars-∈ : {x y : ℕ} {t : Tm} (bs : List (ℕ × Tm)) → (y , t) ∈ bs → x ∈ vars t → x ∈ bvars bs
bvars-∈ ((_ , u) ∷ bs) (here refl) m = any-++ˡ m
bvars-∈ ((_ , u) ∷ bs) (there b)   m = any-++ʳ (vars u) (bvars-∈ bs b m)

-- A variable is bound by the first binding of it, or left alone.
substOf-cases : (bs : List (ℕ × Tm)) (y : ℕ)
              → Σ Tm (λ t → ((y , t) ∈ bs) × (substOf bs y ≡ t)) ⊎ ((substOf bs y ≡ var y) × ¬ (y ∈ map fst bs))
substOf-cases []             y = inr (refl , λ ())
substOf-cases ((z , t) ∷ bs) y with z ≟ y
... | yes refl = inl (t , here refl , refl)
... | no ne with substOf-cases bs y
...   | inl (u , m , e)  = inl (u , there m , e)
...   | inr (e , n)      = inr (e , λ { (here e′) → ne (sym e′) ; (there m) → n m })

substOf-out : (bs : List (ℕ × Tm)) (y : ℕ) → ¬ (y ∈ map fst bs) → substOf bs y ≡ var y
substOf-out bs y n with substOf-cases bs y
... | inl (t , m , e) = ⊥-elim (n (∈-map⁺ fst m))
... | inr (e , _)     = e

-- The variables of a hypothesis.
occH-∈ : (h : RHyp) {x : ℕ} → OccH h x → x ∈ hypVars h
occH-∈ h (inl o) = any-++ˡ (occ-vars (rconcl h) o)
occH-∈ h (inr o) = any-++ʳ (vars (rconcl h)) (occs-varss (rprem h) o)

∈-occH : (h : RHyp) {x : ℕ} → x ∈ hypVars h → OccH h x
∈-occH h m with ∈-++⁻ (vars (rconcl h)) m
... | inl m′ = inl (vars-occ (rconcl h) m′)
... | inr m′ = inr (varss-occs (rprem h) m′)

fixed-∈ : (h : RHyp) {x : ℕ} → Fixed h x → x ∈ fixedVars h
fixed-∈ h (o , n) = ∈-without (hypVars h) (gen h) (occH-∈ h o) n

∈-fixed : (h : RHyp) {x : ℕ} → x ∈ fixedVars h → Fixed h x
∈-fixed h m = ∈-occH h (without-∈ (hypVars h) (gen h) m) , without-∉ (hypVars h) (gen h) m

fixedL-any : (H : List RHyp) {x : ℕ} → x ∈ fixedL H → Any (λ h → Fixed h x) H
fixedL-any (h ∷ hs) m with ∈-++⁻ (fixedVars h) m
... | inl m′ = here (∈-fixed h m′)
... | inr m′ = there (fixedL-any hs m′)

allVarsL-∈ : (C : List RHyp) {x : ℕ} → Any (λ c → OccH c x) C → x ∈ allVarsL C
allVarsL-∈ (c ∷ cs) (here o)  = any-++ˡ (occH-∈ c o)
allVarsL-∈ (c ∷ cs) (there a) = any-++ʳ (hypVars c) (allVarsL-∈ cs a)

-- Positions in a list without repeats.
indexOf-sound : (x : ℕ) (xs : List ℕ) {i : ℕ} → indexOf x xs ≡ just i → lookup xs i ≡ just x
indexOf-sound x []       ()
indexOf-sound x (y ∷ ys) e with x ≟ y
... | yes refl = cong-lookup e
  where
    cong-lookup : {i : ℕ} → just 0 ≡ just i → lookup (x ∷ ys) i ≡ just x
    cong-lookup refl = refl
... | no _ with indexOf x ys in eq
...   | nothing = ⊥-elim (nothing≢just e)
...   | just j  = step e
  where
    step : {i : ℕ} → just (suc j) ≡ just i → lookup (y ∷ ys) i ≡ just x
    step refl = indexOf-sound x ys eq

indexOf-complete : (xs : List ℕ) → Distinct xs → (i : ℕ) {a : ℕ} → lookup xs i ≡ just a → indexOf a xs ≡ just i
indexOf-complete (y ∷ ys) (n ∷ d) zero    refl with y ≟ y
... | yes _ = refl
... | no ne = ⊥-elim (ne refl)
indexOf-complete (y ∷ ys) (n ∷ d) (suc i) {a} e with a ≟ y
... | yes refl = ⊥-elim (n (lookup-∈ ys i e))
... | no _ rewrite indexOf-complete ys d i e = refl

------------------------------------------------------------------------
-- What a goal means, and the boundary between the calculus's hypotheses
-- and a goal's.

module Meaning (Sg : Signature) (R : List Rule) (M : Rules.Model Sg R) where
  open CalculusIn Sg R M
  open ImplicationsIn Sg R M

  -- Every well-sorted ground instance that makes the hypotheses hold in M
  -- makes the judgment hold.
  ValidGoal : Goal → Set
  ValidGoal g = Valid (fst g) (snd g)

  -- Context inclusion: reordering and contraction, never discarding an
  -- undischarged hypothesis.
  weaken : {H K : List RHyp} {J : Tm} → (∀ {h} → h ∈ H → h ∈ K) → ValidR H J → ValidR K J
  weaken {H} {K} {J} inc valid γ gw sats = valid γ gw′ (select H (λ m → m))
    where
      put : ∀ {x h ks} → h ∈ ks → Fixed h x → Any (λ h → Fixed h x) ks
      put (here refl) p = here p
      put (there m)   p = there (put m p)

      fixed : ∀ {x} {hs : List RHyp} → (∀ {h} → h ∈ hs → h ∈ K)
            → Any (λ h → Fixed h x) hs → Any (λ h → Fixed h x) K
      fixed f (here p)  = put (f (here refl)) p
      fixed f (there p) = fixed (λ m → f (there m)) p

      gw′ : GW γ (VarsR H J)
      gw′ x (inl o) = gw x (inl o)
      gw′ x (inr o) = gw x (inr (fixed inc o))

      select : (hs : List RHyp) → (∀ {h} → h ∈ hs → h ∈ H) → All (Sat γ) hs
      select []       f = []
      select (h ∷ hs) f = all-∈ sats (inc (f (here refl))) ∷ select hs (λ m → f (there m))

  plain-fixed : {x : ℕ} (H : List Tm) → Any (λ h → Fixed h x) (map plainR H) → Any (Occ x) H
  plain-fixed (h ∷ hs) (here (inl o , _))  = here o
  plain-fixed (h ∷ hs) (here (inr () , _))
  plain-fixed (h ∷ hs) (there o)           = there (plain-fixed hs o)

  -- Plain hypotheses of the calculus are hypotheses of `Valid`.
  to-valid : {H : List Tm} {J : Tm} → ValidR (map plainR H) J → Valid H J
  to-valid {H} {J} valid γ gw hs = valid γ gw′ (sats H (λ m → m) hs)
    where
      gw′ : GW γ (VarsR (map plainR H) J)
      gw′ x (inl o) = gw x (inl o)
      gw′ x (inr o) = gw x (inr (plain-fixed H o))

      put : ∀ {x p hs} → p ∈ hs → Occ x p → Any (Occ x) hs
      put (here refl) o = here o
      put (there m)   o = there (put m o)

      sats : (ps : List Tm) → (∀ {p} → p ∈ ps → p ∈ H) → All (λ p → Holds (sub γ p)) ps
           → All (Sat γ) (map plainR ps)
      sats []       inc []       = []
      sats (p ∷ ps) inc (d ∷ ds) =
        sat-plain γ p (λ x o → gw x (inr (put (inc (here refl)) o))) d ∷ sats ps (λ m → inc (there m)) ds

------------------------------------------------------------------------
-- Soundness of the checker in a model M

module Sound (Sg : Signature) (R : List Rule) (M : Rules.Model Sg R)
             (wf : All (Matching.RuleWF Sg R) R) (ctors : ℕ → List ℕ)
             (complete : ∀ c x → Signature.out Sg c ≡ Signature.vs Sg x → c ∈ ctors (Signature.vs Sg x)) where
  open Signature Sg
  open CalculusIn Sg R M
  open ImplicationsIn Sg R M
  open Meaning Sg R M
  open Check Sg R ctors
  open Algorithm wf ctors complete using (top-ws; filterOut-∈; concatMap-∈; conclusion-ok; any-witness)
  open Unification Sg R using (mgu-sound; mgu-none)

  -- Invariant: a fact is valid and its judgment well-sorted; a hypothesis's
  -- judgment is well-sorted.
  Good : Fact → Set
  Good (fact hs J) = ValidR (rh hs) J × Σ ℕ (WS J)
  Good (hypo n h)  = WS (rconcl h) (headSort (rconcl h))

  QGood : Hyps × Tm → Set
  QGood q = ValidR (rh (fst q)) (snd q) × Σ ℕ (WS (snd q))

  plain-eq : (h : RHyp) → Plain h → h ≡ plainR (rconcl h)
  plain-eq (rhyp .[] j .[]) (refl , refl) = refl

  premise-ok : (f : Fact) → Good f → {q : Hyps × Tm} → asPremise f ≡ just q → QGood q
  premise-ok (fact hs J) g refl = g
  premise-ok (hypo n h)  w e with when-inv (plain? h) e
  ... | p , refl =
        transport (λ k → ValidR (k ∷ []) (rconcl h)) (sym (plain-eq h p)) (assume-valid (rconcl h))
        , (headSort (rconcl h) , w)

  -- (N (VAR TERM)...): an instance of a hypothesis-free fact.
  instR : {J : Tm} → ValidR [] J → (τ : Subst) → (∀ x → Occ x J → WS (τ x) (vs x)) → ValidR [] (sub τ J)
  instR {J} v τ wτ γ gw [] = transport Holds (sym (sub-comp γ τ J)) (v (γ ∘ˢ τ) gw′ [])
    where
      gw′ : GW (γ ∘ˢ τ) (VarsR [] J)
      gw′ x (inl o) = ground-sub γ (τ x) (λ y oy → fst (gw y (inl (sub-occ τ J o oy))))
                    , ws-sub γ (wτ x o) (λ y oy → snd (gw y (inl (sub-occ τ J o oy))))
      gw′ x (inr ())

  substOf-ws : (bs : List (ℕ × Tm)) → All (λ b → WS (snd b) (vs (fst b))) bs → ∀ x → WS (substOf bs x) (vs x)
  substOf-ws []             []       x = var
  substOf-ws ((y , t) ∷ bs) (w ∷ ws) x with y ≟ x
  ... | yes refl = w
  ... | no _     = substOf-ws bs ws x

  instFact-ok : (bs : List (ℕ × Tm)) (f : Fact) → Good f → {q : Hyps × Tm} → instFact bs f ≡ just q → QGood q
  instFact-ok bs (fact [] j) (v , s , w) e with when-inv (bindsWS? bs) e
  ... | ws , refl = instR v (substOf bs) (λ x _ → substOf-ws bs ws x)
                  , (s , ws-sub (substOf bs) w (λ x _ → substOf-ws bs ws x))
  instFact-ok bs (fact (_ ∷ _) j) g ()
  instFact-ok bs (hypo _ _)       g ()

  resolve-ok : (fs : Facts) → AllT Good fs → (r : Ref) {q : Hyps × Tm} → resolve fs r ≡ just q → QGood q
  resolve-ok fs gf (ref n) e with bind-inv (lookupT fs n) asPremise e
  ... | f , ef , e₁ = premise-ok f (allT-lookup gf n ef) e₁
  resolve-ok fs gf (inR n bs) e with bind-inv (lookupT fs n) (instFact bs) e
  ... | f , ef , e₁ = instFact-ok bs f (allT-lookup gf n ef) e₁

  resolveAll-ok : (fs : Facts) → AllT Good fs → (rs : List Ref) {qs : List (Hyps × Tm)}
                → resolveAll fs rs ≡ just qs → All QGood qs
  resolveAll-ok fs gf []       refl = []
  resolveAll-ok fs gf (r ∷ rs) e
    with bind-inv (resolve fs r) (λ q → resolveAll fs rs >>= λ qs → just (q ∷ qs)) e
  ... | q , e₁ , e₂ with bind-inv (resolveAll fs rs) (λ qs → just (q ∷ qs)) e₂
  ...   | qs , e₃ , refl = resolve-ok fs gf r e₁ ∷ resolveAll-ok fs gf rs e₃

  -- The premises' concatenated hypotheses are among the merged ones.
  allHyps-⊆ : (qs : List (Hyps × Tm)) → ∀ {h} → h ∈ allHyps qs → h ∈ rh (joined qs)
  allHyps-⊆ (q ∷ qs) m with ∈-++⁻ (rh (fst q)) m
  ... | inl m′ = rh-⊆ (merge-l (fst q) (joined qs)) m′
  ... | inr m′ = rh-⊆ (merge-r (fst q) (joined qs)) (allHyps-⊆ qs m′)

  premsR : (θ : Subst) (ps : List Tm) (qs : List (Hyps × Tm)) → subs θ ps ≡ map snd qs → All QGood qs
         → PremsR θ ps (allHyps qs)
  premsR θ []       []       e  []       = []
  premsR θ (p ∷ ps) (q ∷ qs) e  (g ∷ gs) =
    transport (ValidR (rh (fst q))) (sym (∷-head e)) (fst g) ∷ premsR θ ps qs (∷-tail e) gs
  premsR θ []       (q ∷ qs) () _
  premsR θ (p ∷ ps) []       () _

  -- (hyp N (P...) J (X...))
  hyp-ok : (n : ℕ) (ps : List Tm) (j : Tm) (g : List ℕ) {f : Fact} → checkHyp n ps j g ≡ just f → Good f
  hyp-ok n ps j g e with when-inv (ws? j (headSort j)) e
  ... | w , refl = w

  -- A rule's premise variables are bound to parts of well-sorted facts.
  prems-ws : (r : Rule) (c : Env) (ps ts : List Tm) → instsE c ps ≡ just ts → All (PatWF r) ps
           → All (λ t → Σ ℕ (WS t)) ts → ∀ y → Occs y ps → WS (total c y) (rs r y)
  prems-ws r c (p ∷ ps) ts e (pw ∷ pws) wts y o
    with bind-inv (instE c p) (λ t → instsE c ps >>= λ ts′ → just (t ∷ ts′)) e
  ... | t , e₁ , e₂ with bind-inv (instsE c ps) (λ ts′ → just (t ∷ ts′)) e₂
  ...   | ts′ , e₃ , refl with wts | o
  ...     | (s , w) ∷ ws | hd o′ = top-ws r c p (fst pw) e₁ (snd pw) w y o′
  ...     | _ ∷ ws       | tl o′ = prems-ws r c ps ts′ e₃ pws ws y o′

  judgments-ws : (qs : List (Hyps × Tm)) → All QGood qs → All (λ t → Σ ℕ (WS t)) (map snd qs)
  judgments-ws []       []       = []
  judgments-ws (q ∷ qs) (g ∷ gs) = snd g ∷ judgments-ws qs gs

  rule-ok : (fs : Facts) → AllT Good fs → (n : ℕ) (refs : List Ref) (binds : List (ℕ × Tm)) (stated : Maybe Tm)
            {f : Fact} → checkRule fs n refs binds stated ≡ just f → Good f
  rule-ok fs gf n refs binds stated e
    with bind-inv (lookup R n) _ e
  ... | r , er , e₁ with bind-inv (resolveAll fs refs) _ e₁
  ... | qs , eq , e₂ with bind-inv (bindAll r binds empty) _ e₂
  ... | b₀ , eb , e₃ with bind-inv (conclude (concl r) stated b₀) _ e₃
  ... | b₁ , ec , e₄ with bind-inv (matchs (prem r) (map snd qs) b₁) _ e₄
  ... | b₂ , ep , e₅ with bind-inv (answer stated (instE b₂ (concl r))) _ e₅
  ... | J , ea , e₆ with bind-inv (when (all? (λ y → ws? (total b₂ y) (rs r y)) (conclOnly r)) tt) _ e₆
  ... | _ , ew , e₇ with when-inv (all? (λ y → ws? (total b₂ y) (rs r y)) (conclOnly r)) ew
  ... | conclWS , _ with when-inv (allIn? (vars J ++ fixedL (allHyps qs))
                                        (concatMap (λ y → vars (total b₂ y)) (premOnly r))) e₇
  ... | sideAll , refl = valid , (headSort (concl r) , transport (λ t → WS t _) concl-eq wsJ)
    where
      qg : All QGood qs
      qg = resolveAll-ok fs gf refs eq

      wfr : RuleWF r
      wfr = all-lookup n wf er

      θ : Subst
      θ = total b₂

      pm : (b₁ ⊑ b₂) × (instsE b₂ (prem r) ≡ just (map snd qs))
      pm = matchs-ok (prem r) (map snd qs) b₁ ep

      concl-eq : sub θ (concl r) ≡ J
      concl-eq = inst-subst b₂ (concl r) (conclusion-ok (concl r) stated b₀ b₁ b₂ ec (fst pm) ea)

      premWS : ∀ y → Occs y (prem r) → WS (θ y) (rs r y)
      premWS = prems-ws r b₂ (prem r) (map snd qs) (snd pm) (fst wfr) (judgments-ws qs qg)

      wθ : ∀ y → OccR y r → WS (θ y) (rs r y)
      wθ y (inl o) = premWS y o
      wθ y (inr o) with y ∈? varss (prem r)
      ... | yes m = premWS y (varss-occs (prem r) m)
      ... | no nm = all-∈ conclWS (filterOut-∈ (varss (prem r)) (occ-vars (concl r) o) nm)

      wsJ : WS (sub θ (concl r)) (headSort (concl r))
      wsJ = ws-sub′ θ (snd (snd wfr)) (λ y o → wθ y (inr o))

      side : ∀ x → Occs x (subs θ (prem r)) → VarsR (allHyps qs) (sub θ (concl r)) x
      side x o with occs-sub θ (prem r) o
      ... | y , oy , ox with y ∈? vars (concl r)
      ...   | yes m = inl (sub-occ θ (concl r) (vars-occ (concl r) m) ox)
      ...   | no nm with ∈-++⁻ (vars J) (all-∈ sideAll (concatMap-∈ (λ z → vars (θ z))
                           (filterOut-∈ (vars (concl r)) (occs-varss (prem r) oy) nm) (occ-vars (θ y) ox)))
      ...     | inl m′ = inl (transport (Occ x) (sym concl-eq) (vars-occ J m′))
      ...     | inr m′ = inr (fixedL-any (allHyps qs) m′)

      valid : ValidR (rh (joined qs)) J
      valid = weaken (allHyps-⊆ qs)
                (transport (ValidR (allHyps qs)) concl-eq
                  (step-validR (lookup-∈ R n er) θ wθ
                    (premsR θ (prem r) qs (insts-subst b₂ (prem r) (snd pm)) qg) side))

  allMap : {A : Set} {P Q : A → Set} → (∀ {x} → P x → Q x) → {xs : List A} → All P xs → All Q xs
  allMap f []       = []
  allMap f (p ∷ ps) = f p ∷ allMap f ps

  ----------------------------------------------------------------------
  -- apply

  -- The variables a binding or an instantiated premise brings in.
  side-allowed : (J : Tm) (H : List RHyp) (bs : List (ℕ × Tm)) (ps : List Tm) → SideOk J H bs ps
               → ∀ x → x ∈ (varss ps ++ bvars bs) → VarsR H J x
  side-allowed J H bs ps sok x m with ∈-++⁻ (vars J) (all-∈ sok m)
  ... | inl m′ = inl (vars-occ J m′)
  ... | inr m′ = inr (fixedL-any H m′)

  not-bound : (bs : List (ℕ × Tm)) (h : RHyp) → All (λ b → fst b ∈ gen h) bs
            → ∀ x → ¬ (x ∈ gen h) → ¬ (x ∈ map fst bs)
  not-bound ((y , t) ∷ bs) h (g ∷ gs) x n (here refl) = n g
  not-bound ((y , t) ∷ bs) h (g ∷ gs) x n (there m)   = not-bound bs h gs x n m

  applyHyp-ok : (i : ℕ) (h : RHyp) → WS (rconcl h) (headSort (rconcl h)) → (bs : List (ℕ × Tm))
              → All (λ b → WS (snd b) (vs (fst b))) bs → (qs : List (Hyps × Tm)) → All QGood qs
              → {f : Fact} → applyHyp i h bs qs ≡ just f → Good f
  applyHyp-ok i h w bs wbs qs qg e
    with bind-inv (when (all? (λ b → fst b ∈? gen h) bs) tt) _ e
  ... | _ , eg , e₁ with when-inv (all? (λ b → fst b ∈? gen h) bs) eg
  ... | inGen , _ with bind-inv (when (map snd qs ≟ₜs map (sub (substOf bs)) (rprem h)) tt) _ e₁
  ... | _ , epr , e₂ with when-inv (map snd qs ≟ₜs map (sub (substOf bs)) (rprem h)) epr
  ... | prEq , _ with when-inv (sideOk? (sub (substOf bs) (rconcl h)) (h ∷ allHyps qs) bs (map snd qs)) e₂
  ... | sOk , refl = valid , (headSort (rconcl h) , ws-sub (substOf bs) w (λ x _ → substOf-ws bs wbs x))
    where
      σ : Subst
      σ = substOf bs

      J′ : Tm
      J′ = sub σ (rconcl h)

      psEq : subs σ (rprem h) ≡ map snd qs
      psEq = trans (subs-map σ (rprem h)) (sym prEq)

      allowed : ∀ x → x ∈ (varss (map snd qs) ++ bvars bs) → VarsR (h ∷ allHyps qs) J′ x
      allowed = side-allowed J′ (h ∷ allHyps qs) bs (map snd qs) sOk

      inPs : ∀ {x} → Occs x (subs σ (rprem h)) → VarsR (h ∷ allHyps qs) J′ x
      inPs {x} o = allowed x (any-++ˡ (occs-varss (map snd qs) (transport (Occs x) psEq o)))

      side : ∀ x → (Occs x (subs σ (rprem h)) ⊎ Σ ℕ (λ y → (y ∈ gen h) × OccH h y × Occ x (σ y)))
           → VarsR (h ∷ allHyps qs) J′ x
      side x (inl o) = inPs o
      side x (inr (y , g , oy , ox)) with substOf-cases bs y
      ... | inl (t , b , et) =
            allowed x (any-++ʳ (varss (map snd qs)) (bvars-∈ bs b (occ-vars t (transport (Occ x) et ox))))
      ... | inr (et , _) with transport (Occ x) et ox
      ...   | here with oy
      ...     | inl oc = inl (occ-keep σ (rconcl h) et oc)
      ...     | inr op = inPs (occs-keep σ (rprem h) et op)

      inc : ∀ {k} → k ∈ (h ∷ allHyps qs) → k ∈ rh (merge ((i , h) ∷ []) (joined qs))
      inc (here refl) = rh-⊆ (merge-l ((i , h) ∷ []) (joined qs)) (here refl)
      inc (there m)   = rh-⊆ (merge-r ((i , h) ∷ []) (joined qs)) (allHyps-⊆ qs m)

      valid : ValidR (rh (merge ((i , h) ∷ []) (joined qs))) J′
      valid = weaken inc (apply-hyp-valid h σ (λ x n → substOf-out bs x (not-bound bs h inGen x n))
                            (λ x _ _ → substOf-ws bs wbs x) (premsR σ (rprem h) qs psEq qg) side)

  plains-ok : (hs : List RHyp) {Ps : List Tm} → plains hs ≡ just Ps → hs ≡ map plainR Ps
  plains-ok []       refl = refl
  plains-ok (h ∷ hs) e with bind-inv (when (plain? h) (rconcl h)) _ e
  ... | p , ep , e₁ with when-inv (plain? h) ep
  ... | pl , refl with bind-inv (plains hs) _ e₁
  ... | ps , eps , refl = cong₂ _∷_ (plain-eq h pl) (plains-ok hs eps)

  applyFact-ok : (hs : Hyps) (J : Tm) → Good (fact hs J) → (bs : List (ℕ × Tm))
               → All (λ b → WS (snd b) (vs (fst b))) bs → (qs : List (Hyps × Tm)) → All QGood qs
               → {f : Fact} → applyFact hs J bs qs ≡ just f → Good f
  applyFact-ok hs J (v , s , w) bs wbs qs qg e
    with bind-inv (plains (rh hs)) _ e
  ... | Ps , ep , e₁ with bind-inv (when (map snd qs ≟ₜs map (sub (substOf bs)) Ps) tt) _ e₁
  ... | _ , epr , e₂ with when-inv (map snd qs ≟ₜs map (sub (substOf bs)) Ps) epr
  ... | prEq , _ with when-inv (sideOk? (sub (substOf bs) J) (allHyps qs) bs (map snd qs)) e₂
  ... | sOk , refl = valid , (s , ws-sub (substOf bs) w (λ x _ → substOf-ws bs wbs x))
    where
      σ : Subst
      σ = substOf bs

      J′ : Tm
      J′ = sub σ J

      psEq : subs σ Ps ≡ map snd qs
      psEq = trans (subs-map σ Ps) (sym prEq)

      allowed : ∀ x → x ∈ (varss (map snd qs) ++ bvars bs) → VarsR (allHyps qs) J′ x
      allowed = side-allowed J′ (allHyps qs) bs (map snd qs) sOk

      inPs : ∀ {x} → Occs x (subs σ Ps) → VarsR (allHyps qs) J′ x
      inPs {x} o = allowed x (any-++ˡ (occs-varss (map snd qs) (transport (Occs x) psEq o)))

      side : ∀ x → (Occs x (subs σ Ps) ⊎ Σ ℕ (λ y → VarsR (map plainR Ps) J y × Occ x (σ y)))
           → VarsR (allHyps qs) J′ x
      side x (inl o) = inPs o
      side x (inr (y , vy , ox)) with substOf-cases bs y
      ... | inl (t , b , et) =
            allowed x (any-++ʳ (varss (map snd qs)) (bvars-∈ bs b (occ-vars t (transport (Occ x) et ox))))
      ... | inr (et , _) with transport (Occ x) et ox
      ...   | here with vy
      ...     | inl oj = inl (occ-keep σ J et oj)
      ...     | inr a  = inPs (occs-keep σ Ps et (any-occs (plain-fixed Ps a)))

      valid : ValidR (rh (joined qs)) J′
      valid = weaken (allHyps-⊆ qs)
                (apply-fact-valid (transport (λ H → ValidR H J) (plains-ok (rh hs) ep) v) σ
                  (λ x _ → substOf-ws bs wbs x) (premsR σ Ps qs psEq qg) side)

  applyTo-ok : (f : Fact) → Good f → (bs : List (ℕ × Tm)) → All (λ b → WS (snd b) (vs (fst b))) bs
             → (qs : List (Hyps × Tm)) → All QGood qs → {g : Fact} → applyTo f bs qs ≡ just g → Good g
  applyTo-ok (hypo i h)  w = applyHyp-ok i h w
  applyTo-ok (fact hs J) g = applyFact-ok hs J g

  apply-ok : (fs : Facts) → AllT Good fs → (m : ℕ) (bs : List (ℕ × Tm)) (refs : List Ref)
           → {f : Fact} → checkApply fs m bs refs ≡ just f → Good f
  apply-ok fs gf m bs refs e with bind-inv (when (bindsWS? bs) tt) _ e
  ... | _ , ew , e₁ with when-inv (bindsWS? bs) ew
  ... | wbs , _ with bind-inv (lookupT fs m) _ e₁
  ... | f , ef , e₂ with bind-inv (resolveAll fs refs) _ e₂
  ... | qs , eq , e₃ = applyTo-ok f (allT-lookup gf m ef) bs wbs qs (resolveAll-ok fs gf refs eq) e₃

  ----------------------------------------------------------------------
  -- induct

  case-sem : (X : ℕ) (Ps : List Tm) (J : Tm) (c : ℕ) (ys : List ℕ) (q : Hyps × Tm) → QGood q
           → CaseOk X Ps J c ys (fst q) (snd q) → SemCaseR X Ps J c
  case-sem X Ps J c ys q g (sorts , dist , fresh , jeq , hs) =
    semcaseR ys dist sorts (allMap fr fresh) (rh (fst q)) (allMap conv hs)
             (transport (ValidR (rh (fst q))) jeq (fst g))
    where
      fr : ∀ {y} → ¬ (y ∈ (vars J ++ varss Ps)) → ¬ (Occ y J ⊎ Occs y Ps)
      fr n (inl o) = n (any-++ˡ (occ-vars J o))
      fr n (inr o) = n (any-++ʳ (vars J) (occs-varss Ps o))

      conv : ∀ {h} → CaseH X Ps J c ys h → CaseHyp X Ps J c ys h
      conv (inl m) with ∈-map⁻ (λ p → plainR (sub (point X (node c (map var ys))) p)) Ps m
      ... | p , mp , refl = premise mp
      conv {h} (inr (a , disj)) with any-witness a
      ... | y , my , (sy , heq) =
            transport (CaseHyp X Ps J c ys) (sym heq) (ih y my sy (gen h) (λ g mg → all-∈ disj mg))

  cases-ok : (fs : Facts) → AllT Good fs → (X : ℕ) (Ps : List Tm) (J : Tm) (cs : List ℕ)
             (ks : List (ℕ × List ℕ)) → checkCases fs X Ps J cs ks ≡ just tt → All (SemCaseR X Ps J) cs
  cases-ok fs gf X Ps J []       []              refl = []
  cases-ok fs gf X Ps J (c ∷ cs) ((m , ys) ∷ ks) e
    with bind-inv (lookupT fs m >>= asPremise) _ e
  ... | q , eq , e₁ with bind-inv (lookupT fs m) asPremise eq
  ... | f , ef , epq with bind-inv (when (caseOk? X Ps J c ys (fst q) (snd q)) tt) _ e₁
  ... | _ , ew , e₂ with when-inv (caseOk? X Ps J c ys (fst q) (snd q)) ew
  ... | okc , _ =
        case-sem X Ps J c ys q (premise-ok f (allT-lookup gf m ef) epq) okc ∷ cases-ok fs gf X Ps J cs ks e₂
  cases-ok fs gf X Ps J []       (k ∷ ks)        ()
  cases-ok fs gf X Ps J (c ∷ cs) []              ()

  rh-asHyps : (ps : List (ℕ × Tm)) → rh (asHyps ps) ≡ map plainR (map snd ps)
  rh-asHyps []       = refl
  rh-asHyps (p ∷ ps) = cong (plainR (snd p) ∷_) (rh-asHyps ps)

  induct-ok : (fs : Facts) → AllT Good fs → (X : ℕ) (is : List ℕ) (J : Tm) (ks : List (ℕ × List ℕ))
            → {f : Fact} → checkInduct fs X is J ks ≡ just f → Good f
  induct-ok fs gf X is J ks e
    with bind-inv (plainHyps fs is) _ e
  ... | ps , _ , e₁ with bind-inv (when (ws? J (headSort J)) tt) _ e₁
  ... | _ , ewj , e₂ with when-inv (ws? J (headSort J)) ewj
  ... | wJ , _ with bind-inv (when (X ∈? (vars J ++ varss (map snd ps))) tt) _ e₂
  ... | _ , em , e₃ with when-inv (X ∈? (vars J ++ varss (map snd ps))) em
  ... | mX , _ with bind-inv (checkCases fs X (map snd ps) J (ctors (vs X)) ks) _ e₃
  ... | _ , ec , refl = valid , (headSort J , wJ)
    where
      oX : Occ X J ⊎ Occs X (map snd ps)
      oX with ∈-++⁻ (vars J) mX
      ... | inl m = inl (vars-occ J m)
      ... | inr m = inr (varss-occs (map snd ps) m)

      valid : ValidR (rh (asHyps ps)) J
      valid = transport (λ H → ValidR H J) (sym (rh-asHyps ps))
                (InductionR.induction X (map snd ps) J oX
                  (λ c ce → all-∈ (cases-ok fs gf X (map snd ps) J (ctors (vs X)) ks ec) (complete c X ce)))

  ----------------------------------------------------------------------
  -- invert

  plainHyp-ok : (f : Fact) → Good f → {kh : ℕ × Tm} → plainHyp f ≡ just kh → WS (snd kh) (headSort (snd kh))
  plainHyp-ok (hypo n h)  w e with when-inv (plain? h) e
  ... | _ , refl = w
  plainHyp-ok (fact _ _)  g ()

  ruleVars-occ : (r : Rule) {y : ℕ} → OccR y r → y ∈ ruleVars r
  ruleVars-occ r (inl o) = any-++ˡ (occs-varss (prem r) o)
  ruleVars-occ r (inr o) = any-++ʳ (varss (prem r)) (occ-vars (concl r) o)

  occ-ruleVars : (r : Rule) {y : ℕ} → y ∈ ruleVars r → OccR y r
  occ-ruleVars r m with ∈-++⁻ (varss (prem r)) m
  ... | inl m′ = inl (varss-occs (prem r) m′)
  ... | inr m′ = inr (vars-occ (concl r) m′)

  used-∈ : (h J : Tm) (C : List RHyp) {x : ℕ} → Used h J C x → x ∈ usedVars h J C
  used-∈ h J C (inl o)       = any-++ˡ (occ-vars h o)
  used-∈ h J C (inr (inl o)) = any-++ʳ (vars h) (any-++ˡ (occ-vars J o))
  used-∈ h J C (inr (inr a)) = any-++ʳ (vars h) (any-++ʳ (vars J) (allVarsL-∈ C a))

  -- A list of fresh, distinct variables renames a rule apart.
  rename-apart : (r : Rule) (xs : List ℕ) (h J : Tm) (C : List RHyp) → RenOk r xs (usedVars h J C)
           → Renaming r (Used h J C)
  rename-apart r xs h J C (dist , defined , fresh) = mkRenaming (renF xs) (backF r xs) back-rn rn-back fresh′
    where
      at-y : ∀ y → y ∈ ruleVars r → lookup xs y ≡ just (renF xs y)
      at-y y m with all-∈ defined m
      ... | a , la = trans la (cong just (sym (lookup-nth xs y 0 la)))

      back-rn : ∀ y → OccR y r → backF r xs (renF xs y) ≡ just y
      back-rn y o rewrite indexOf-complete xs dist y (at-y y (ruleVars-occ r o)) with y ∈? ruleVars r
      ... | yes _ = refl
      ... | no n  = ⊥-elim (n (ruleVars-occ r o))

      rn-back : ∀ x y → backF r xs x ≡ just y → (x ≡ renF xs y) × OccR y r
      rn-back x y e with bind-inv (indexOf x xs) _ e
      ... | i , ei , e₁ with when-inv (i ∈? ruleVars r) e₁
      ... | m , refl = sym (lookup-nth xs i 0 (indexOf-sound x xs ei)) , occ-ruleVars r m

      fresh′ : ∀ y → OccR y r → ¬ Used h J C (renF xs y)
      fresh′ y o u = all-∈ fresh (lookup-∈ xs y (at-y y (ruleVars-occ r o))) (used-∈ h J C u)

  okOf-inv : (o : Outcome) {θ : Subst} → okOf o ≡ just θ → o ≡ ok θ
  okOf-inv (ok θ) refl = refl
  okOf-inv none   ()
  okOf-inv stuck  ()

  inv-allowed : (θ : Subst) (xs : List ℕ) (r : Rule) (C : List RHyp) {k : RHyp}
              → k ∈ allowedInv θ xs r C → InvHyp θ (renF xs) r C k
  inv-allowed θ xs r C m with ∈-++⁻ (map (λ p → plainR (sub θ (sub (renS xs) p))) (prem r)) m
  ... | inl a with ∈-map⁻ (λ p → plainR (sub θ (sub (renS xs) p))) (prem r) a
  ...   | p , mp , refl = premise mp
  inv-allowed θ xs r C m | inr a with ∈-map⁻ (appθ θ) C a
  ...   | c , mc , refl = context mc

  invCase-ok : (fs : Facts) → AllT Good fs → (h J : Tm) (C : List RHyp) → WS h (headSort h)
             → (r : Rule) (xs : List ℕ) (m : ℕ) → invCase fs h J C r xs m ≡ just tt → RuleCase h J C r
  invCase-ok fs gf h J C wh r xs m e
    with bind-inv (when (renOk? r xs (usedVars h J C)) tt) _ e
  ... | _ , er , e₁ with when-inv (renOk? r xs (usedVars h J C)) er
  ... | rok , _ with bind-inv (when (sorted? r xs) tt) _ e₁
  ... | _ , es , e₂ with when-inv (sorted? r xs) es
  ... | srt , _ with bind-inv (when (ws? (sub (renS xs) (concl r)) (headSort h)) tt) _ e₂
  ... | _ , ewc , e₃ with when-inv (ws? (sub (renS xs) (concl r)) (headSort h)) ewc
  ... | wc , _ with bind-inv (okOf (mgu fuel h (sub (renS xs) (concl r)))) _ e₃
  ... | θ , eθ , e₄ with bind-inv (when (noCap? C θ) tt) _ e₄
  ... | _ , enc , e₅ with when-inv (noCap? C θ) enc
  ... | nc , _ with bind-inv (lookupT fs m >>= asPremise) _ e₅
  ... | q , eq , e₆ with bind-inv (lookupT fs m) asPremise eq
  ... | f , ef , epq with bind-inv (when (snd q ≟ₜ sub θ J) tt) _ e₆
  ... | _ , ej , e₇ with when-inv (snd q ≟ₜ sub θ J) ej
  ... | jeq , _ with when-inv (all? (λ k → k ∈ʰ? allowedInv θ xs r C) (rh (fst q))) e₇
  ... | alw , _ =
        rulecase (rename-apart r xs h J C rok)
          (inr (invcase (λ y o → all-∈ srt (ruleVars-occ r o)) θ
                  (mgu-sound fuel h (sub (renS xs) (concl r)) wh wc (okOf-inv _ eθ))
                  noCapture (rh (fst q)) (allMap (inv-allowed θ xs r C) alw)
                  (transport (ValidR (rh (fst q))) jeq (fst (premise-ok f (allT-lookup gf m ef) epq)))))
    where
      noCapture : ∀ c → c ∈ C → ∀ x → Fixed c x → ∀ g → g ∈ gen c → ¬ Occ g (θ x)
      noCapture c mc x fx g mg o = all-∈ (all-∈ (all-∈ nc mc) (fixed-∈ c fx)) mg (occ-vars (θ x) o)

  noCase-ok : (h J : Tm) (C : List RHyp) (r : Rule) → noCase h J C r ≡ just tt → RuleCase h J C r
  noCase-ok h J C r e
    with bind-inv (when (renOk? r (freshFor (usedVars h J C) r) (usedVars h J C)) tt) _ e
  ... | _ , er , e₁ with when-inv (renOk? r (freshFor (usedVars h J C) r) (usedVars h J C)) er
  ... | rok , _ with when-inv (isNone? (mgu fuel h (sub (renS (freshFor (usedVars h J C) r)) (concl r)))) e₁
  ... | nu , _ =
        rulecase (rename-apart r (freshFor (usedVars h J C) r) h J C rok)
          (inl (mgu-none fuel h (sub (renS (freshFor (usedVars h J C) r)) (concl r)) nu))

  ruleCase-ok : (fs : Facts) → AllT Good fs → (h J : Tm) (C : List RHyp) → WS h (headSort h)
              → (ks : List (ℕ × (ℕ × List ℕ))) (i : ℕ) (r : Rule) → ruleCase fs h J C ks i r ≡ just tt
              → RuleCase h J C r
  ruleCase-ok fs gf h J C wh ks i r e with clash? h (concl r)
  ... | yes (f , ts , g , us , eh , ec , ne) = clash eh ec ne
  ... | no _ with findCase i ks
  ...   | just (m , xs) = invCase-ok fs gf h J C wh r xs m e
  ...   | nothing       = noCase-ok h J C r e

  allRules-ok : (fs : Facts) → AllT Good fs → (h J : Tm) (C : List RHyp) → WS h (headSort h)
              → (ks : List (ℕ × (ℕ × List ℕ))) (i : ℕ) (rs : List Rule) → allRules fs h J C ks i rs ≡ just tt
              → ∀ r → r ∈ rs → RuleCase h J C r
  allRules-ok fs gf h J C wh ks i []        e r ()
  allRules-ok fs gf h J C wh ks i (r′ ∷ rs) e r m
    with bind-inv (ruleCase fs h J C ks i r′) _ e
  ... | _ , e₁ , e₂ with m
  ...   | here refl = ruleCase-ok fs gf h J C wh ks i r′ e₁
  ...   | there m′  = allRules-ok fs gf h J C wh ks (suc i) rs e₂ r m′

  invert-ok : (fs : Facts) → AllT Good fs → (k : ℕ) (is : List ℕ) (J : Tm) (ks : List (ℕ × (ℕ × List ℕ)))
            → {f : Fact} → checkInvert fs k is J ks ≡ just f → Good f
  invert-ok fs gf k is J ks e
    with bind-inv (lookupT fs k >>= plainHyp) _ e
  ... | kh , ekh , e₁ with bind-inv (lookupT fs k) plainHyp ekh
  ... | f , ef , epk with bind-inv (ctxHyps fs is) _ e₁
  ... | C , _ , e₂ with bind-inv (when (ws? J (headSort J)) tt) _ e₂
  ... | _ , ewj , e₃ with when-inv (ws? J (headSort J)) ewj
  ... | wJ , _ with bind-inv (allRules fs (snd kh) J (rh C) ks 0 R) _ e₃
  ... | _ , ea , refl = valid , (headSort J , wJ)
    where
      K : Hyps
      K = (fst kh , plainR (snd kh)) ∷ []

      inc : ∀ {h} → h ∈ (plainR (snd kh) ∷ rh C) → h ∈ rh (merge C K)
      inc (here refl) = rh-⊆ (merge-r C K) (here refl)
      inc (there m)   = rh-⊆ (merge-l C K) m

      valid : ValidR (rh (merge C K)) J
      valid = weaken inc (invert-valid (snd kh) J (rh C)
                (allRules-ok fs gf (snd kh) J (rh C) (plainHyp-ok f (allT-lookup gf k ef) epk) ks 0 R ea))

  ----------------------------------------------------------------------
  -- Steps, goals, the certificate

  step-ok : (fs : Facts) → AllT Good fs → (n : ℕ) (s : Form) {f : Fact} → checkStep fs n s ≡ just f → Good f
  step-ok fs gf n (hypF ps j g)               e = hyp-ok n ps j g e
  step-ok fs gf n (ruleF r refs binds stated) e = rule-ok fs gf r refs binds stated e
  step-ok fs gf n (applyF m bs refs)          e = apply-ok fs gf m bs refs e
  step-ok fs gf n (inductF X is J ks)         e = induct-ok fs gf X is J ks e
  step-ok fs gf n (invertF k is J ks)         e = invert-ok fs gf k is J ks e

  stream-ok : (T : TmTable) (fs : Facts) → AllT Good fs → (n k : ℕ) (c : Code) {r : Facts × Code}
            → checkStream T fs n k c ≡ just r → AllT Good (fst r)
  stream-ok T fs gf n zero    c refl = gf
  stream-ok T fs gf n (suc k) c e with bind-inv (formP T c) _ e
  ... | r , e₁ , e₂ with bind-inv (checkStep fs n (fst r)) _ e₂
  ...   | f , e₃ , e₄ = stream-ok T (insertT fs n f) (allT-insert gf (step-ok fs gf n (fst r) e₃) n) (suc n) k (snd r) e₄

  goals-ok : (T : TmTable) (fs : Facts) → AllT Good fs → (gs : List Goal) (c : Code)
           → checkGoals T fs gs c ≡ just tt → All ValidGoal gs
  goals-ok T fs gf []       c refl = []
  goals-ok T fs gf (g ∷ gs) c e with bind-inv (refP T c) _ e
  ... | r , e₁ , e₂ with bind-inv (resolve fs (fst r)) _ e₂
  ... | q , e₃ , e₄ with bind-inv (when (goalOk? (fst q) (snd q) g) tt) _ e₄
  ... | _ , e₅ , e₆ with when-inv (goalOk? (fst q) (snd q) g) e₅
  ... | (jeq , inc) , _ =
        to-valid (weaken (λ m → all-∈ inc m) (transport (ValidR (rh (fst q))) jeq (fst (resolve-ok fs gf (fst r) e₃))))
        ∷ goals-ok T fs gf gs (snd r) e₆

  -- Main theorem: if Agda evaluates `accepts goals c` to `just tt`, each
  -- goal's hypotheses imply its judgment at every well-sorted ground
  -- instance, in the model M.
  accepts-sound : (goals : List Goal) (c : Code) → accepts goals c ≡ just tt → All ValidGoal goals
  accepts-sound goals c e with bind-inv (num c) _ e
  ... | r₁ , _ , e₁ with bind-inv (table (fst r₁) 0 leaf (snd r₁)) _ e₁
  ... | r₂ , _ , e₂ with bind-inv (num (snd r₂)) _ e₂
  ... | r₃ , _ , e₃ with bind-inv (checkStream (fst r₂) leaf 0 (fst r₃) (snd r₃)) _ e₃
  ... | r₄ , e₄ , e₅ = goals-ok (fst r₂) (fst r₄) (stream-ok (fst r₂) leaf leaf 0 (fst r₃) (snd r₃) e₄) goals (snd r₄) e₅

------------------------------------------------------------------------
-- Changing the sorts of variables
--
-- A certificate's signature gives sorts to all its variables; a theorem
-- stated for the goal alone may declare only the goal's. Ground terms have
-- the same sorts under both when the symbols agree, so a model under one
-- is a model under the other, and a goal valid under one is valid under
-- the other when the two agree on its variables.

module Ground (Sg Sg′ : Signature) (R : List Rule)
              (same-out : ∀ f → Signature.out Sg f ≡ Signature.out Sg′ f)
              (same-ins : ∀ f → Signature.ins Sg f ≡ Signature.ins Sg′ f) where
  private
    module A = Rules Sg R
    module B = Rules Sg′ R

  mutual
    ground-ws : {t : Tm} {s : ℕ} → Ground t → A.WS t s → B.WS t s
    ground-ws g A.var = ⊥-elim (g _ here)
    ground-ws {node f ts} g (A.node e w) =
      B.node (trans (sym (same-out f)) e)
             (transport (B.WSs ts) (same-ins f) (ground-wss (λ x o → g x (arg o)) w))

    ground-wss : {ts : List Tm} {ss : List ℕ} → (∀ x → ¬ Occs x ts) → A.WSs ts ss → B.WSs ts ss
    ground-wss g A.[]         = B.[]
    ground-wss g (w A.∷ ws) = ground-ws (λ x o → g x (hd o)) w B.∷ ground-wss (λ x o → g x (tl o)) ws

  gws : {t : Tm} {s : ℕ} → A.GroundWS t s → B.GroundWS t s
  gws (g , w) = g , ground-ws g w

module Transfer (Sg Sg′ : Signature) (R : List Rule)
                (same-out : ∀ f → Signature.out Sg f ≡ Signature.out Sg′ f)
                (same-ins : ∀ f → Signature.ins Sg f ≡ Signature.ins Sg′ f) where
  private
    module A = Rules Sg R
    module B = Rules Sg′ R
    open module G = Ground Sg Sg′ R same-out same-ins using (gws)
    module G⁻ = Ground Sg′ Sg R (λ f → sym (same-out f)) (λ f → sym (same-ins f))

  model : A.Model → B.Model
  model M = record
    { holds   = A.Model.holds M
    ; closure = λ r∈R σ okr ps → A.Model.closure M r∈R σ (λ y o → G⁻.gws (okr y o)) ps
    ; support = λ d → support′ (A.Model.support M d)
    }
    where
      support′ : {t : Tm} → Σ Rule (λ r → (r ∈ R) × Σ Subst (λ σ →
                   (∀ y → A.OccR y r → A.GroundWS (σ y) (rs r y)) × All (λ p → A.Model.holds M (sub σ p)) (prem r)
                   × (t ≡ sub σ (concl r))))
               → Σ Rule (λ r → (r ∈ R) × Σ Subst (λ σ →
                   (∀ y → B.OccR y r → B.GroundWS (σ y) (rs r y)) × All (λ p → A.Model.holds M (sub σ p)) (prem r)
                   × (t ≡ sub σ (concl r))))
      support′ (r , m , σ , okr , ps , e) = r , m , σ , (λ y o → gws (okr y o)) , ps , e

  -- A goal valid under Sg′ in the transferred model is valid under Sg.
  valid-back : (M : A.Model) {H : List Tm} {J : Tm}
             → (∀ x → CalculusIn.Vars Sg R M H J x → Signature.vs Sg x ≡ Signature.vs Sg′ x)
             → CalculusIn.Valid Sg′ R (model M) H J → CalculusIn.Valid Sg R M H J
  valid-back M agree v γ gw hs =
    v γ (λ x o → transport (B.GroundWS (γ x)) (agree x o) (gws (gw x o))) hs
