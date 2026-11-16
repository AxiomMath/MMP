module

public import MMP.AlgebraicGeometry.MMP.Fourfold.StratumAdjunction
public import MMP.AlgebraicGeometry.Singularities.Discrepancy.Basic

/-!
# Crepant birational maps, pluriforms and admissible section systems

Let `(X, B)` be a pair of a normal variety and a `ℚ`-divisor, and `D = K_X + B`. A birational map
`φ : (X, B) ⇢ (X', B')` is *crepant* if it preserves every divisorial log discrepancy; its
pull-back `φ^*` acts on rational (meromorphic) `m`-fold top forms, and the space
`V_m = H⁰(X, mD)` consists of the `m`-fold top forms with poles and zeros prescribed by `mB`.
The crepant birational self-maps of `(X, B)` form a group. In the source `X` is smooth projective
and `B` an snc subboundary; `T = B^{=1}` is the reduced coefficient-one divisor.

For a finite collection of normal projective rational dlt pairs `(X_i, B_i)` of the same
dimension and a sufficiently divisible even `m`, a section system is a tuple
`s_i ∈ H⁰(X_i, m(K_{X_i} + B_i))`. Restricting by iterated Poincaré residues along a flag of
strata `V ⊆ X_i` gives a section of `m(K_V + B_V)` on the adjunction pair `(V, B_V)`. The system
is *admissible* if the residue restrictions to any two strata of the same dimension (whole
components included) correspond by pluriform pull-back along every crepant birational map between
their adjunction pairs, and *preadmissible* if this is required for proper strata only.

## Main definitions

* `MMP.Fourfold.logPluricanonicalSections`: `H⁰(X, m(K_X + B))` as a `k`-subspace of the
  rational `m`-canonical forms.
* `MMP.Fourfold.pluriformPullback`: pull-back of `m`-canonical forms along a `k`-homomorphism of
  function fields.
* `MMP.Fourfold.IsCrepantBirationalMap`: crepant birational maps between pairs.
* `MMP.Fourfold.crepantBirationalAutomorphisms`: the group of crepant birational self-maps.
* `MMP.Fourfold.IsSNCSubboundaryPair`, `MMP.Fourfold.coeffOnePart`: the snc setting and
  `T = B^{=1}`.
* `MMP.Fourfold.IsIteratedResidue`: Poincaré residues of `m`-fold forms
  (`MMP.Fourfold.IsPoincareResidue`) iterated along a flag of strata.
* `MMP.Fourfold.IsStratifiedSectionSetting`, `MMP.Fourfold.ResidueRestriction`: the setting of a
  finite collection of dlt pairs, and residue restriction maps to their strata.
* `MMP.Fourfold.admissibleSections`, `MMP.Fourfold.preadmissibleSections`: the admissible and
  preadmissible section systems, as `k`-subspaces of `⊕ᵢ H⁰(X_i, m(K_{X_i} + B_i))`.

## Implementation notes

* A birational map `φ : X ⇢ X'` of varieties is recorded by its pull-back, a `k`-isomorphism
  `σ = φ^* : k(X') ≅ k(X)` (`MMP.Fourfold.FunctionFieldEquiv`). The source defines crepant maps
  through a common resolution identifying the crepant boundaries of the two pairs, with
  compatible canonical forms, and notes that this is equivalent to preserving every divisorial
  log discrepancy; the definition here is the second formulation, with the log discrepancy
  `MMP.Intersection.IsLogDiscrepancy`: `v` has log discrepancy `a` on `(X, B)` if and only if
  `v ∘ σ` has log discrepancy `a` on `(X', B')`.
* `H⁰(X, m(K_X + B))` is the space of global sections of `𝒪_X(mK_X + ⌊mB⌋)`
  (`MMP.Mori.pluricanonicalSections`); in the source `mB` is integral, and then `⌊mB⌋ = mB`.
  It is a `k`-subspace for the `k`-structure of the rational forms restricted from `k(X)`.
  The definitions are made for any normal variety and `ℚ`-divisor; smoothness, projectivity
  and the snc condition of the source are recorded in `MMP.Fourfold.IsSNCSubboundaryPair`.
* The Poincaré residue is characterised in the local ring `𝒪_{Y,y}` at the generic point `y`
  of the divisor: if `τ = g · (dt/t ∧ dx₁ ∧ ⋯ ∧ dx_n)^{⊗m}` with `t` a uniformizer, then
  `Res τ = ḡ · (dx̄₁ ∧ ⋯ ∧ dx̄_n)^{⊗m}`. Strata are the final strata of flags of iterated
  adjunction (`MMP.Fourfold.StratumAdjunctionData`), each carrying its adjunction pair
  `(S, B_S)`; a whole component is the flag of length zero, and a proper stratum is reached by a
  flag of positive length. All flags reaching a stratum are allowed; for even `m` the ordering
  signs of iterated residues cancel.
* The residue restriction maps are not constructed: `MMP.Fourfold.ResidueRestriction` carries,
  for every flag, a `k`-linear map sending each section to its iterated residue along the flag
  (`MMP.Fourfold.IsIteratedResidue`), which determines it. The admissible and preadmissible
  subspaces are defined from these maps.
* The base field is any field; the source works over `ℂ`. Rational dlt pairs
  (`MMP.Fourfold.IsPair`) are over an algebraically closed field of characteristic zero.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open scoped WithZero

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

universe u

namespace MMP.Fourfold

open MMP.Mori

section Forms

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]

/-- The `k`-vector space structure of the rational `m`-canonical forms of an integral scheme over
`k`, restricted from their `k(X)`-vector space structure. -/
instance RationalPluriForms.instModuleBase (d : ℕ) (m : ℤ) : Module k (RationalPluriForms sX d m) :=
  letI := functionFieldAlgebra sX
  Module.compHom _ (algebraMap k X.functionField)

/-- A scalar `c : k` acts on rational pluricanonical forms through its image in the function
field. -/
theorem RationalPluriForms.smul_def {d : ℕ} {m : ℤ} (c : k) (τ : RationalPluriForms sX d m) :
    c • τ = (letI := functionFieldAlgebra sX; algebraMap k X.functionField c) • τ :=
  rfl

variable {sX}

/-- A nonzero constant does not change the order of a rational form along a prime divisor. -/
theorem ordForm_const_smul [IsLocallyNoetherian X] (Γ : Mori.PrimeDivisor X) {d : ℕ}
    {m : ℤ} {c : k} (hc : c ≠ 0) (τ : RationalPluriForms sX d m) :
    Γ.ordForm (c • τ) = Γ.ordForm τ := by
  classical
  let := stalkAlgebra sX Γ.genericPoint
  let := functionFieldAlgebra sX
  have := isScalarTower_stalk_functionField sX Γ.genericPoint
  have hu : X.ord (algebraMap k X.functionField c) Γ.genericPoint = 0 := by
    rw [IsScalarTower.algebraMap_apply k Γ.localRing X.functionField]
    exact Γ.ord_algebraMap_of_isUnit ((IsUnit.mk0 c hc).map _)
  unfold PrimeDivisor.ordForm ordAt
  split_ifs with h
  · rw [RationalPluriForms.smul_def]
    erw [formCoeff_smul]
    by_cases hτ : formCoeff Γ.localRing h.choose_spec.1 h.choose_spec.2 τ = 0
    · rw [hτ, mul_zero]
    · have hc' : algebraMap k X.functionField c ≠ 0 := by simpa using hc
      exact (Γ.ord_mul_of_ne_zero _ _ hc' hτ).trans (by rw [hu, zero_add])
  · rfl

end Forms

/-! ### Pull-back of forms along field homomorphisms -/

section PullbackForms

variable {k : Type*} [CommRing k] {K K' : Type*} [Field K] [Field K'] [Algebra k K]
  [Algebra k K'] [Algebra K K'] [IsScalarTower k K K'] {d : ℕ} {m : ℤ}

/-- Pull-back of pluricanonical forms along a field extension is additive. -/
theorem pullbackForms_add (τ τ' : PluriForms k K d m) :
    pullbackForms (K' := K') m (τ + τ') = pullbackForms m τ + pullbackForms m τ' := by
  unfold pullbackForms
  split_ifs with h
  · simp [pullbackFormsAlong, add_smul]
  · simp

/-- Pull-back of pluricanonical forms along `K → K'` sends `f • τ` to the image of `f` in `K'`
acting on the pull-back of `τ`. -/
theorem pullbackForms_smul (f : K) (τ : PluriForms k K d m) :
    pullbackForms (K' := K') m (f • τ) = algebraMap K K' f • pullbackForms m τ := by
  unfold pullbackForms
  split_ifs with h
  · simp [pullbackFormsAlong, mul_smul]
  · simp

end PullbackForms

section Sections

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X]

/-- **The log pluricanonical sections** `H⁰(X, m(K_X + B))` of a `ℚ`-divisor `B` on a normal
variety `X`, for `m ∈ ℕ`: the rational `m`-canonical forms `τ` with
`ord_Γ(τ) + ⌊m b_Γ⌋ ≥ 0` for every prime divisor `Γ`, that is, the global sections of
`𝒪_X(mK_X + ⌊mB⌋)` (`MMP.Mori.pluricanonicalSections`), as a `k`-subspace of the rational
`m`-canonical forms. When `mB` is integral these are the meromorphic `m`-fold top forms with
poles bounded by `mB` (zeros prescribed where `B` is negative). -/
@[mmp "def_fourfold_crepant_pluriform_action"]
def logPluricanonicalSections (d m : ℕ) (B : QDivisor X) :
    Submodule k (RationalPluriForms sX d m) where
  __ := (pluricanonicalSections sX d m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) ⊤).toAddSubmonoid
  smul_mem' c τ hτ := by
    by_cases hc : c = 0
    · subst hc
      rw [zero_smul]
      exact zero_mem (pluricanonicalSections sX d m _ ⊤)
    refine ⟨fun hU => by rw [hτ.1 hU, smul_zero], fun Γ hΓ hne => ?_⟩
    have hτ0 : τ ≠ 0 := fun h => hne (by rw [h, smul_zero])
    rw [ordForm_const_smul Γ hc]
    exact hτ.2 Γ hΓ hτ0

/-- A rational form lies in `logPluricanonicalSections sX d m B` if and only if it is a global
section of `𝒪_X(mK_X + ⌊mB⌋)`. -/
theorem mem_logPluricanonicalSections {d m : ℕ} {B : QDivisor X} {τ : RationalPluriForms sX d m} :
    τ ∈ logPluricanonicalSections sX d m B ↔
      τ ∈ pluricanonicalSections sX d m (DivisorWithCoeffs.roundDown ((m : ℤ) • B)) ⊤ :=
  Iff.rfl

end Sections

/-! ### Birational maps, crepant birational maps and the pluriform action -/

section Crepant

variable {k : Type u} [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  (sX' : X' ⟶ Spec (.of k)) [IsIntegral X] [IsIntegral X']

/-- The `k`-isomorphisms `k(X') ≅ k(X)` of function fields of integral schemes over `k`. For
varieties these are the pull-backs `φ^*` of the birational maps `φ : X ⇢ X'`. -/
abbrev FunctionFieldEquiv : Type u :=
  @AlgEquiv k X'.functionField X.functionField _ _ _ (functionFieldAlgebra sX')
    (functionFieldAlgebra sX)

/-- The `k`-homomorphisms `k(X') → k(X)` of function fields of integral schemes over `k`. -/
abbrev FunctionFieldHom : Type u :=
  @AlgHom k X'.functionField X.functionField _ _ _ (functionFieldAlgebra sX')
    (functionFieldAlgebra sX)

/-- A `k`-isomorphism of function fields as a `k`-homomorphism. -/
abbrev FunctionFieldEquiv.toHom (σ : FunctionFieldEquiv sX sX') : FunctionFieldHom sX sX' :=
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra sX
  σ.toAlgHom

/-- **Pluriform pull-back.** The pull-back `φ^* : ω^{⊗m}_{k(X')} → ω^{⊗m}_{k(X)}` of rational
`m`-canonical forms along a `k`-homomorphism of function fields `φ : k(X') → k(X)`
(`MMP.Mori.pullbackForms`), a `k`-linear map. For a birational map `X ⇢ X'` this is the action of
pull-back on meromorphic `m`-fold top forms. -/
@[mmp "def_fourfold_crepant_pluriform_action"]
def pluriformPullback (φ : FunctionFieldHom sX sX') (d : ℕ) (m : ℤ) :
    RationalPluriForms sX' d m →ₗ[k] RationalPluriForms sX d m where
  toFun τ :=
    letI := functionFieldAlgebra sX'
    letI := functionFieldAlgebra sX
    letI : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    haveI : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    pullbackForms (K := X'.functionField) (K' := X.functionField) m τ
  map_add' τ τ' := by
    let := functionFieldAlgebra sX'
    let := functionFieldAlgebra sX
    let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    have : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    exact pullbackForms_add (K := X'.functionField) (K' := X.functionField) (d := d) (m := m) τ τ'
  map_smul' c τ := by
    let := functionFieldAlgebra sX'
    let := functionFieldAlgebra sX
    let : Algebra X'.functionField X.functionField := φ.toRingHom.toAlgebra
    have : IsScalarTower k X'.functionField X.functionField :=
      IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
    have h := pullbackForms_smul (k := k) (K := X'.functionField) (K' := X.functionField)
      (d := d) (m := m) (algebraMap k X'.functionField c) τ
    rw [← IsScalarTower.algebraMap_apply] at h
    exact h

variable [IsLocallyNoetherian X] [IsNormal X] [IsLocallyNoetherian X'] [IsNormal X']

/-- A valuation `v` of `k(X)` *has log discrepancy `a`* with respect to a `ℚ`-divisor `B` if it
is the valuation of a divisor `(Y, f, E)` over `X` (with `f` proper) whose log discrepancy
`a(E, X, B)` (`MMP.Intersection.IsLogDiscrepancy`) is `a`. -/
def HasLogDiscrepancy (B : QDivisor X) (v : Valuation X.functionField ℤᵐ⁰) (a : ℝ) : Prop :=
  ∃ (n : ℕ) (D : DivisorOver k sX), D.valuation = v ∧
    MMP.Intersection.IsLogDiscrepancy sX n (QDivisor.toRDivisor B) D a

/-- **Crepant birational maps.** A birational map `φ : (X, B) ⇢ (X', B')` of pairs, given by its
pull-back `σ = φ^* : k(X') ≅ k(X)`, is *crepant* if it preserves every divisorial log
discrepancy: a valuation `v` of `k(X)` has log discrepancy `a` with respect to `(X, B)` if and
only if the valuation `v ∘ σ` of `k(X')` has log discrepancy `a` with respect to `(X', B')`.
Since `v ↦ v ∘ σ` is a bijection between the valuations of `k(X)` and of `k(X')`, this says that
`φ` identifies the divisorial valuations of the two pairs together with their log
discrepancies. For `X' = X`, `B' = B` these are the *crepant birational self-maps* of `(X, B)`. -/
@[mmp "def_fourfold_crepant_pluriform_action"]
def IsCrepantBirationalMap (B : QDivisor X) (B' : QDivisor X') (σ : FunctionFieldEquiv sX sX') :
    Prop :=
  letI := functionFieldAlgebra sX'
  letI := functionFieldAlgebra sX
  ∀ (v : Valuation X.functionField ℤᵐ⁰) (a : ℝ),
    HasLogDiscrepancy sX B v a ↔
      HasLogDiscrepancy sX' B' (v.comap (σ.toRingEquiv.toRingHom)) a

variable (B : QDivisor X)

/-- **Crepant birational self-maps.** The crepant birational self-maps of a pair `(X, B)`
(`MMP.Fourfold.IsCrepantBirationalMap` with `(X', B') = (X, B)`), as a subgroup of the group of
`k`-automorphisms of `k(X)`. -/
@[mmp "def_fourfold_crepant_pluriform_action"]
def crepantBirationalAutomorphisms : Subgroup (FunctionFieldEquiv sX sX) where
  carrier := {σ | IsCrepantBirationalMap sX sX B B σ}
  one_mem' v a := Iff.rfl
  mul_mem' {σ τ} hσ hτ v a := (hσ v a).trans (hτ _ a)
  inv_mem' {σ} hσ v a := by
    let := functionFieldAlgebra sX
    have h := hσ (v.comap (σ⁻¹ : FunctionFieldEquiv sX sX).toRingEquiv.toRingHom) a
    have hv : (v.comap (σ⁻¹ : FunctionFieldEquiv sX sX).toRingEquiv.toRingHom).comap
        σ.toRingEquiv.toRingHom = v := by
      ext x
      change v (σ⁻¹ (σ x)) = v x
      rw [← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
    rw [hv] at h
    exact h.symm

end Crepant

section SNC

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))

/-- The setting of crepant pluriforms: `X` is a smooth projective variety over `k` and `B` is a
`ℚ`-divisor with simple normal crossing support whose coefficients are all at most one (an snc
subboundary; coefficients may be negative). -/
@[mmp "def_fourfold_crepant_pluriform_action"]
structure IsSNCSubboundaryPair (B : QDivisor X) : Prop where
  /-- `X` is a projective variety over `k`. -/
  isProjectiveVariety : Mori.IsProjectiveVariety k sX
  /-- `X` is smooth over `k`. -/
  isSmoothScheme : IsSmoothScheme sX
  /-- `B` has simple normal crossing support. -/
  isSNC : DivisorWithCoeffs.IsSNC sX B
  /-- Every coefficient of `B` is at most one. -/
  coeff_le_one : ∀ P, B.coeff P ≤ 1

variable {sX}

/-- The *reduced coefficient-one part* `T = B^{=1}` of a `ℚ`-divisor `B`: the reduced divisor
whose components are the prime divisors along which `B` has coefficient one. -/
@[mmp "def_fourfold_crepant_pluriform_action"]
def coeffOnePart (B : QDivisor X) : Divisor X :=
  Finsupp.mapRange (fun q : ℚ => if q = 1 then (1 : ℤ) else 0) (by simp) B

/-- The coefficient of `coeffOnePart B` along a prime divisor `P` is `1` if `B` has
coefficient one along `P`, and `0` otherwise. -/
theorem coeff_coeffOnePart (B : QDivisor X) (P : Mori.PrimeDivisor X) :
    (coeffOnePart B).coeff P = if B.coeff P = 1 then 1 else 0 :=
  Finsupp.mapRange_apply

end SNC

/-! ### Iterated residues along a flag of strata -/

namespace StratumAdjunctionData

variable {k : Type u} [Field k] {X : Scheme.{u}} {sX : X ⟶ Spec (.of k)}
  [IsLocallyNoetherian X] [IsNormal X] {B : QDivisor X} {S : Scheme.{u}} {ι : S ⟶ X}
  {BS : QDivisor S}

/-- The final stratum of a flag is integral. -/
theorem isIntegral_stratum (F : StratumAdjunctionData sX B ι BS) : IsIntegral S :=
  F.isNormalVariety.1.toIsIntegral

/-- The final stratum of a flag is normal. -/
theorem isNormal_stratum (F : StratumAdjunctionData sX B ι BS) : IsNormal S :=
  F.isNormalVariety.2

/-- The final stratum of a flag is locally Noetherian. -/
theorem isLocallyNoetherian_stratum (F : StratumAdjunctionData sX B ι BS) :
    IsLocallyNoetherian S :=
  haveI := F.isNormalVariety.1.toLocallyOfFiniteType
  LocallyOfFiniteType.isLocallyNoetherian (ι ≫ sX)

end StratumAdjunctionData

section IteratedResidue

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [IsIntegral X]
  [IsLocallyNoetherian X] [IsNormal X] (B : QDivisor X)

/-- **Iterated residues along a flag of strata.** For a rational `m`-canonical form `τ` of degree
`n` on `X` and a flag `X = S₀ ⊃ S₁ ⊃ ⋯ ⊃ S_k = S` of iterated adjunction data of `(X, B)`
(`MMP.Fourfold.StratumAdjunctionData`), `IsIteratedResidue sX B τ F e ρ` says that the form `ρ`
of degree `e` on `S` is obtained from `τ` by taking Poincaré residues
(`MMP.Fourfold.IsPoincareResidue`) successively along `S₁ ⊂ S₀`, …, `S_k ⊂ S_{k-1}`; then
`e = n - k`. The form `τ` on `S₀ = X` is regarded as a form for the structure morphism
`𝟙 ≫ s_X`. -/
@[mmp "def_fourfold_stratified_admissible_sections"]
inductive IsIteratedResidue {n m : ℕ} (τ : RationalPluriForms sX n m) :
    ∀ {S : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} [IsIntegral S],
      StratumAdjunctionData sX B ι BS → (e : ℕ) → RationalPluriForms (ι ≫ sX) e m → Prop
  /-- On the flag of length zero, the residue of `τ` is `τ`. -/
  | refl (h : MMP.Mori.IsPair sX B) :
      IsIteratedResidue τ (.refl h) n (cast (by rw [Category.id_comp]) τ)
  /-- One more Poincaré residue along an adjunction step `T ⊂ S`. -/
  | step {S T : Scheme.{u}} {ι : S ⟶ X} {BS : QDivisor S} [IsIntegral S] [IsLocallyNoetherian S]
      [IsIntegral T] {F : StratumAdjunctionData sX B ι BS} {j : T ⟶ S} {BT : QDivisor T}
      {hj : IsAdjunctionStep (ι ≫ sX) BS j BT} {e : ℕ} {ρ : RationalPluriForms (ι ≫ sX) (e + 1) m}
      {ρ' : RationalPluriForms (j ≫ ι ≫ sX) e m} (hF : IsIteratedResidue τ F (e + 1) ρ)
      (hr : IsPoincareResidue (ι ≫ sX) j e m ρ ρ') :
      IsIteratedResidue τ (.step F j BT hj) e (cast (by rw [Category.assoc]) ρ')

end IteratedResidue

/-! ### Admissible section systems on a finite collection of dlt pairs -/

section Admissible

variable {k : Type u} [Field k] {I : Type*} {X : I → Scheme.{u}} (sX : ∀ i, X i ⟶ Spec (.of k))
  [∀ i, IsIntegral (X i)] [∀ i, IsLocallyNoetherian (X i)] [∀ i, IsNormal (X i)]
  (B : ∀ i, QDivisor (X i)) (n m : ℕ)

/-- **The setting of stratified admissibility.** A finite collection of normal projective
rational dlt pairs `(X_i, B_i)` (`MMP.Fourfold.IsPair`, `MMP.Intersection.IsDltPair`) of the same
dimension `n`, together with an even integer `m > 0` making the adjoint `m(K_S + B_S)` Cartier
for every adjunction pair `(S, B_S)` on a stratum of some `X_i`, reached by a flag of iterated
adjunction (`MMP.Fourfold.StratumAdjunctionData`); the flag of length zero gives the adjoints
`m(K_{X_i} + B_i)` themselves. -/
@[mmp "def_fourfold_stratified_admissible_sections"]
structure IsStratifiedSectionSetting : Prop where
  /-- The collection of pairs is finite. -/
  finite : Finite I
  /-- Each `X_i` is a projective variety. -/
  isProjectiveVariety : ∀ i, Mori.IsProjectiveVariety k (sX i)
  /-- Each `(X_i, B_i)` is a pair. -/
  isPair : ∀ i, IsPair (sX i) (B i)
  /-- Each `(X_i, B_i)` is a dlt pair. -/
  isDltPair : ∀ i, MMP.Intersection.IsDltPair (sX i) (B i)
  /-- Each `X_i` has dimension `n`. -/
  topologicalKrullDim_eq : ∀ i, topologicalKrullDim (X i) = n
  /-- The multiple `m` is even. -/
  even : Even m
  /-- The multiple `m` is positive. -/
  pos : 0 < m
  /-- For every adjunction pair `(S, B_S)` on a stratum of `X_i`, the divisor `m(K_S + B_S)` is
  Cartier for some canonical divisor `K_S`. -/
  isCartierDivisor : ∀ (i : I) {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS),
    haveI := F.isIntegral_stratum
    haveI := F.isNormal_stratum
    haveI := F.isLocallyNoetherian_stratum
    ∃ (d : ℕ) (K : Divisor S), K.IsCanonicalDivisor (ι ≫ sX i) d ∧
      ((m : ℤ) • (Divisor.toQDivisor K + BS)).IsCartierDivisor

/-- **Residue restrictions of sections to strata.** In the setting
`MMP.Fourfold.IsStratifiedSectionSetting`, for every pair `(X_i, B_i)`, every flag `F` of
iterated adjunction with final stratum `S` and every `e`, a `k`-linear map from
`H⁰(X_i, m(K_{X_i} + B_i))` to the rational `m`-canonical forms of degree `e` on `S` which, when
`e = dim S`, sends each section to its iterated Poincaré residue along `F`
(`MMP.Fourfold.IsIteratedResidue`): the residue restriction of a section to the stratum, a
section of `m(K_S + B_S)`. -/
@[mmp "def_fourfold_stratified_admissible_sections"]
structure ResidueRestriction where
  /-- The pairs `(X_i, B_i)` and the multiple `m` form a stratified section setting. -/
  setting : IsStratifiedSectionSetting sX B n m
  /-- The residue restriction along a flag, in degree `e`. -/
  toFun : ∀ (i : I) {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ),
    haveI := F.isIntegral_stratum
    logPluricanonicalSections (sX i) n m (B i) →ₗ[k] RationalPluriForms (ι ≫ sX i) e m
  /-- In degree `e = dim S`, the residue restriction of a section along `F` is its iterated
  Poincaré residue along `F`. -/
  isIteratedResidue : ∀ (i : I) {S : Scheme.{u}} {ι : S ⟶ X i} {BS : QDivisor S}
    (F : StratumAdjunctionData (sX i) (B i) ι BS) (e : ℕ)
    (τ : logPluricanonicalSections (sX i) n m (B i)), topologicalKrullDim S = e →
    haveI := F.isIntegral_stratum
    IsIteratedResidue (sX i) (B i) (τ : RationalPluriForms (sX i) n m) F e (toFun i F e τ)

variable {sX B n m}

/-- The section systems `(s_i) ∈ ⊕ᵢ H⁰(X_i, m(K_{X_i} + B_i))` whose residue restrictions
correspond by pluriform pull-back along every crepant birational map between the adjunction
pairs of two strata of the same dimension reached by flags of length at least `ℓ`. -/
def residueCompatibleSections (R : ResidueRestriction sX B n m) (ℓ : ℕ) :
    Submodule k (∀ i, logPluricanonicalSections (sX i) n m (B i)) where
  carrier := {s | ∀ (i i' : I) {S S' : Scheme.{u}} {ι : S ⟶ X i} {ι' : S' ⟶ X i'}
    {BS : QDivisor S} {BS' : QDivisor S'} (F : StratumAdjunctionData (sX i) (B i) ι BS)
    (F' : StratumAdjunctionData (sX i') (B i') ι' BS') (e : ℕ),
    ℓ ≤ F.length → ℓ ≤ F'.length → topologicalKrullDim S = e → topologicalKrullDim S' = e →
    haveI := F.isIntegral_stratum
    haveI := F.isNormal_stratum
    haveI := F.isLocallyNoetherian_stratum
    haveI := F'.isIntegral_stratum
    haveI := F'.isNormal_stratum
    haveI := F'.isLocallyNoetherian_stratum
    ∀ σ : FunctionFieldEquiv (ι ≫ sX i) (ι' ≫ sX i'),
      IsCrepantBirationalMap (ι ≫ sX i) (ι' ≫ sX i') BS BS' σ →
      pluriformPullback (ι ≫ sX i) (ι' ≫ sX i') σ.toHom e m (R.toFun i' F' e (s i')) =
        R.toFun i F e (s i)}
  add_mem' {s t} hs ht i i' S S' ι ι' BS BS' F F' e h₁ h₂ h₃ h₄ σ hσ := by
    simp only [Pi.add_apply, map_add, hs i i' F F' e h₁ h₂ h₃ h₄ σ hσ,
      ht i i' F F' e h₁ h₂ h₃ h₄ σ hσ]
  zero_mem' i i' S S' ι ι' BS BS' F F' e h₁ h₂ h₃ h₄ σ hσ := by
    simp only [Pi.zero_apply, map_zero]
  smul_mem' c s hs i i' S S' ι ι' BS BS' F F' e h₁ h₂ h₃ h₄ σ hσ := by
    simp only [Pi.smul_apply, map_smul, hs i i' F F' e h₁ h₂ h₃ h₄ σ hσ]

/-- **Admissible section systems.** A section system `(s_i)`,
`s_i ∈ H⁰(X_i, m(K_{X_i} + B_i))`, is *admissible* if for every two strata `V ⊆ X_i`,
`W ⊆ X_j` of the same dimension, including whole components, and every crepant birational map
`φ : (V, B_V) ⇢ (W, B_W)` between their adjunction pairs, the residue restrictions correspond by
pluriform pull-back: `φ^*(s_j|_W) = s_i|_V`. The admissible systems form a `k`-subspace of
`⊕ᵢ H⁰(X_i, m(K_{X_i} + B_i))`. -/
@[mmp "def_fourfold_stratified_admissible_sections"]
def admissibleSections (R : ResidueRestriction sX B n m) :
    Submodule k (∀ i, logPluricanonicalSections (sX i) n m (B i)) :=
  residueCompatibleSections R 0

/-- **Preadmissible section systems.** The condition of
`MMP.Fourfold.admissibleSections` imposed only for proper strata (flags of positive length). -/
@[mmp "def_fourfold_stratified_admissible_sections"]
def preadmissibleSections (R : ResidueRestriction sX B n m) :
    Submodule k (∀ i, logPluricanonicalSections (sX i) n m (B i)) :=
  residueCompatibleSections R 1

/-- Every admissible section system is preadmissible. -/
theorem admissibleSections_le_preadmissibleSections (R : ResidueRestriction sX B n m) :
    admissibleSections R ≤ preadmissibleSections R :=
  fun _ hs i i' _ _ _ _ _ _ F F' e _ _ => hs i i' F F' e (Nat.zero_le _) (Nat.zero_le _)

end Admissible

end MMP.Fourfold
