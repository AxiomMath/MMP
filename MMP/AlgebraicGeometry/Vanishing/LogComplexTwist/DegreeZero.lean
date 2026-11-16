module

public import MMP.AlgebraicGeometry.Vanishing.LogComplexTwist.Basic

/-!
# The degree-zero term of the fractional logarithmic complex

Let `π : V ⟶ Spec ℂ` be smooth, `D` a relative simple normal crossing divisor, `M` a divisor and
`U' = V ∖ (D ∪ Supp M)`. A model `(K, F, e, ι)` of the fractional logarithmic complex
`C^• = 𝒪_V(-M) · Ω^•_V(log D)(-S)` with `S = 0` has degree-zero term
`C^0 = 𝒪_V(-M) · 𝒪_V = 𝒪_V(-M)`: a section of `F 0` over `W` is, through `ι`, a function `g` on
`W ∩ U'`, locally of the form `∑ aᵢ hᵢ` with `aᵢ` sections of `𝒪_V(-M)` and `hᵢ` regular, hence
the restriction of a unique section of `𝒪_V(-M)` over `W`: every irreducible component of `V`
meets `U'`, so a rational function on `W` is determined by its restriction to `W ∩ U'`, and
membership in `𝒪_V(-M)` is local. Conversely a section `a` of `𝒪_V(-M)` over `W` is regular on
`W ∩ U'`, where `M` has no component (algebraic Hartogs), and the function it gives there is
the image of a section of `F 0`.

For two models `K` (for `M`) and `K'` (for `M'`) with the same `U'` and `-M' ≤ -M`, and a
morphism `φ : K' ⟶ K` commuting with the embeddings into the forms on `U ∩ W ∩ U'`, the
degree-zero component of `φ` is therefore the inclusion `𝒪_V(-M') ⟶ 𝒪_V(-M)`. This applies to
the twist `M' = M + k D`, `k ≥ 0`, for which `U'` does not change.

## Main definitions

* `MMP.LcBpf.degreeZeroIso`: `F 0 ≅ 𝒪_V(-M)` for a model of `C^•` with `S = 0`.
* `MMP.LcBpf.degreeZeroRestrictIso`: `K.X 0 ≅ 𝒪_V(-M)`, as sheaves of `π⁻¹𝒪`-modules.

## Main results

* `MMP.LcBpf.degreeZeroIso_hom_app`: the isomorphism sends a section `x` to the rational
  function restricting, on `W ∩ U'`, to the function `ι x`.
* `MMP.LcBpf.exists_iso_divisorialSheaf_of_isCModel`: `F 0 ≅ 𝒪_V(-M)`, compatibly with `ι` and
  the embedding of `𝒪_V(-M)` into the rational functions.
* `MMP.LcBpf.degreeZeroIso_comp_twist`, `MMP.LcBpf.degreeZeroRestrictIso_comp_twist`: in degree
  zero, a morphism of models commuting with the embeddings is the inclusion
  `𝒪_V(-M') ⟶ 𝒪_V(-M)`.

## Implementation notes

* A degree-zero form on an open of `U = V ∖ D` is `c · 1` for a function `c`, through the
  identification `Ω^0 ≅ 𝒪`; it is compared with sections of `𝒪_V(-M)` through its image `sm c`
  in the total ring of forms, on which `sm` is injective.
* The two opens `U ∩ W ∩ U'` of the models for `M` and `M'` agree only propositionally, so the
  forms of `K'` are transported to those of `K` by a restriction map along an equality of opens.

## References

* [H. Esnault, E. Viehweg, *Lectures on vanishing theorems*][EsnaultViehweg1992]
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace MMP.LcBpf

open MMP.Mori MMP.FourfoldProofs.FractionalLogComplexProof

universe u

section GenericPoints

variable {X : Scheme.{u}}

/-- The generic point of an irreducible component of `X` lies outside the support of every
divisor. -/
theorem componentGenericPoint_notMem_supp {R : Type*} [Zero R] (D : DivisorWithCoeffs R X)
    (Z : irreducibleComponents X) : componentGenericPoint X Z ∉ D.supp := by
  intro h
  obtain ⟨E, -, hE⟩ := DivisorWithCoeffs.mem_supp_iff.mp h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hE
  have h1 : E.genericPoint ⤳ componentGenericPoint X Z := specializes_iff_mem_closure.mpr hE
  have hZ := isGenericPoint_componentGenericPoint X Z
  have hmax : Order.coheight (componentGenericPoint X Z) = 0 := by
    rw [Order.coheight_eq_zero]
    intro b hb
    have hb' : b ⤳ componentGenericPoint X Z := hb
    have h1 : Z.1 ⊆ closure {b} := by
      rw [← hZ.def]
      exact hb'.closure_subset
    have h2 : closure {b} ⊆ Z.1 := Z.2.2 isIrreducible_singleton.closure h1
    have h3 : b ∈ closure {componentGenericPoint X Z} := by
      rw [hZ.def]
      exact h2 (subset_closure rfl)
    exact specializes_iff_mem_closure.mpr h3
  have h2 : componentGenericPoint X Z ⤳ E.genericPoint :=
    (Order.coheight_eq_zero.mp hmax) (b := E.genericPoint) h1
  have heq : E.genericPoint = componentGenericPoint X Z := (h1.antisymm h2).eq
  have := E.coheight_genericPoint
  rw [heq, hmax] at this
  exact zero_ne_one this

/-- The generic point of every irreducible component of `X` lies in `U' = X ∖ (D ∪ Supp M)`. -/
theorem componentGenericPoint_mem_cU' (D M : Divisor X) (Z : irreducibleComponents X) :
    componentGenericPoint X Z ∈ cU' D M := by
  change componentGenericPoint X Z ∉ ((D.supp ⊔ M.supp : Closeds X) : Set X)
  rw [Closeds.coe_sup]
  rintro (h | h)
  · exact componentGenericPoint_notMem_supp D Z h
  · exact componentGenericPoint_notMem_supp M Z h

/-- If an open `A` contains the generic point of every irreducible component, restriction of
rational functions from `W` to `W ∩ A` is injective. -/
theorem rationalFunctionsPresheaf_map_inf_injective {W A : X.Opens}
    (hA : ∀ Z, componentGenericPoint X Z ∈ A) :
    Function.Injective
      ((rationalFunctionsPresheaf X).map (homOfLE (inf_le_left : W ⊓ A ≤ W)).op) := by
  intro a b h
  funext Z
  exact congrFun h ⟨Z.1, ⟨Z.2, hA Z.1⟩⟩

end GenericPoints

section Forms

variable {Y T : Scheme.{u}} (g : Y ⟶ T)

/-- The image `sm c` of a function `c` in the total ring of forms is the degree-zero form
`c · 1`. -/
theorem sm_eq_incl_smul_one (O : Y.Opens) (c : Γ(Y, O)) :
    sm g O c = (TB g).incl ((0 : ℕ) : ℤ)
      ((show (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O) from c) •
        (TB g).one.eval (op O)) := by
  change (show (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace).obj.obj (op O) from c) •
    (1 : (TB g).Total (op O)) = _
  rw [Stacks.GradedAlgebra.one_eq_incl, ← Stacks.GradedAlgebra.incl_smul]
  rfl

/-- Every degree-zero form on `O` is `sm c` for some function `c` on `O`. -/
theorem exists_incl_zero_eq_sm (O : Y.Opens)
    (ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece ((0 : ℕ) : ℤ)).val.obj (op O)) :
    ∃ c : Γ(Y, O), (TB g).incl ((0 : ℕ) : ℤ) ω = sm g O c := by
  obtain ⟨c, hc⟩ := (Scheme.Hom.deRhamAlgebras g).exists_exterior_eq_smul_one (op O) ω
  exact ⟨c, (congrArg ((TB g).incl ((0 : ℕ) : ℤ)) hc.symm).trans (sm_eq_incl_smul_one g O c).symm⟩

/-- The inclusion of the degree-`p` forms into the total ring of forms is injective. -/
theorem formsIncl_injective (O : Y.Opens) (p : ℤ) :
    Function.Injective (fun x : ((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece p).val.obj
      (op O) => (TB g).incl p x) := fun _ _ h =>
  DirectSum.of_injective (β := fun i =>
    (((Scheme.Hom.relativeDifferentialFormsAlgebra g).piece i).val.obj (op O) : Type u)) p h

/-- The map `sm` from functions on `O` to the total ring of forms is injective. -/
theorem sm_injective (O : Y.Opens) : Function.Injective (sm g O) := by
  intro a b h
  rw [sm_eq_incl_smul_one, sm_eq_incl_smul_one] at h
  have h2 := formsIncl_injective g O _ h
  have h3 := congrArg ((Scheme.Hom.deRhamAlgebras g).exteriorPieceZeroIsoUnit.hom.val.app (op O))
    h2
  have key : ∀ r : (Sheaf.toRingCat (Opens.grothendieckTopology Y) Y.sheaf).obj.obj (op O),
      (Scheme.Hom.deRhamAlgebras g).exteriorPieceZeroIsoUnit.hom.val.app (op O)
      (r • (Scheme.Hom.deRhamAlgebras g).exterior.one.eval (op O)) = r := fun r => by
    rw [map_smul, (Scheme.Hom.deRhamAlgebras g).exteriorPieceZeroIsoUnit_one (op O)]
    exact mul_one r
  exact (key a).symm.trans (h3.trans (key b))

end Forms

section App

variable {X : Scheme.{u}}

/-- For an open `A ≤ U`, the map `Γ(X, A) → Γ(U, U.ι⁻¹ A)` induced by the open immersion `U.ι` is
bijective. -/
theorem ι_app_bijective (U A : X.Opens) (hA : A ≤ U) : Function.Bijective (U.ι.app A) := by
  have : IsIso (U.ι.app A) :=
    Scheme.Hom.isIso_app U.ι A (by rw [Scheme.Opens.opensRange_ι]; exact hA)
  exact (ConcreteCategory.isIso_iff_bijective _).mp this

end App

section DivCond

variable {X : Scheme.{u}} [IsLocallyNoetherian X] [IsNormal X] {D M : Divisor X}

/-- The zero function satisfies `DivCond`. -/
theorem divCond_zero (W' : X.Opens) : DivCond (D := D) (M := M) W' 0 :=
  ⟨0, zero_mem _, by rw [map_zero, map_zero]⟩

/-- `DivCond` is closed under addition. -/
theorem divCond_add {W' : X.Opens} {g g' : Γ(X, W' ⊓ cU' D M)}
    (hg : DivCond (D := D) (M := M) W' g) (hg' : DivCond (D := D) (M := M) W' g') :
    DivCond (D := D) (M := M) W' (g + g') := by
  obtain ⟨a, ha, he⟩ := hg
  obtain ⟨a', ha', he'⟩ := hg'
  exact ⟨a + a', add_mem ha ha', by rw [map_add, map_add, he, he']⟩

/-- `DivCond` is closed under finite sums. -/
theorem divCond_sum {W' : X.Opens} {ι : Type*} (s : Finset ι) (g : ι → Γ(X, W' ⊓ cU' D M))
    (h : ∀ i ∈ s, DivCond (D := D) (M := M) W' (g i)) :
    DivCond (D := D) (M := M) W' (∑ i ∈ s, g i) :=
  Finset.sum_induction _ _ (fun _ _ => divCond_add) (divCond_zero W') h

/-- `DivCond` is closed under multiplication by the restriction of a regular function on `W'`. -/
theorem divCond_mul {W' : X.Opens} {g : Γ(X, W' ⊓ cU' D M)} (c : Γ(X, W'))
    (hg : DivCond (D := D) (M := M) W' g) :
    DivCond (D := D) (M := M) W' (g * X.presheaf.map (homOfLE inf_le_left).op c) := by
  obtain ⟨a, ha, he⟩ := hg
  refine ⟨c • a, Submodule.smul_mem _ c ha, ?_⟩
  rw [rationalFunctionsPresheaf_map_smul, he, Algebra.smul_def, map_mul, mul_comm]
  rfl

/-- `DivCond` is local on `W`: a function on `W ∩ U'` whose restrictions to the opens of a cover
of `W` satisfy `DivCond` satisfies `DivCond` on `W`. -/
theorem divCond_of_local {W : X.Opens} {g : Γ(X, W ⊓ cU' D M)}
    (H : ∀ y ∈ W, ∃ (W' : X.Opens) (h : W' ≤ W), y ∈ W' ∧
      DivCond (D := D) (M := M) W' (X.presheaf.map (homOfLE (inf_le_inf_right _ h)).op g)) :
    DivCond (D := D) (M := M) W g := by
  let a : ToType ((rationalFunctionsPresheaf X).obj (op W)) := fun Z =>
    (toRationalFunctionsPresheaf X).app (op (W ⊓ cU' D M)) g
      ⟨Z.1, ⟨Z.2, componentGenericPoint_mem_cU' D M Z.1⟩⟩
  refine ⟨a, fun E hE => ?_, rfl⟩
  obtain ⟨y, hyE, hyW⟩ := id hE
  obtain ⟨W', hW', hyW', a', ha', he'⟩ := H y hyW
  have hE' : (E.support ∩ W').Nonempty := ⟨y, hyE, hyW'⟩
  have key := ha' E hE'
  have hval := congrFun he' ⟨E.component, ⟨E.componentGenericPoint_mem_of_nonempty hE',
    componentGenericPoint_mem_cU' D M _⟩⟩
  rw [toRationalFunctionsPresheaf_app_map] at hval
  have hval' : a' ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE'⟩ =
      a ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩ := hval
  change E.OrdGE _ (a ⟨E.component, E.componentGenericPoint_mem_of_nonempty hE⟩)
  rwa [← hval']

end DivCond

section Restrict

variable {X T : Scheme.{u}} (f : X ⟶ T) (D M : Divisor X)

/-- Restricting a degree-zero form on `U ∩ B` along `A ≤ B` restricts the function it is equal
to. -/
theorem incl_map_eq_sm {A B : X.Opens} (h : A ≤ B)
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((0 : ℕ) : ℤ)).val.obj (op ((cU D).ι ⁻¹ᵁ B))} {g : Γ(X, B)}
    (hg : (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) ω =
      sm ((cU D).ι ≫ f) ((cU D).ι ⁻¹ᵁ B) ((cU D).ι.app B g)) :
    (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ)
        (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
          ((0 : ℕ) : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono _ h)).op ω) =
      sm ((cU D).ι ≫ f) ((cU D).ι ⁻¹ᵁ A) ((cU D).ι.app A (X.presheaf.map (homOfLE h).op g)) := by
  refine (incl_map f D _ _ ω).trans ?_
  rw [hg]
  refine (totalRestrict_sm _ _).trans ?_
  exact congrArg _ (G1.app_restrict h g)

/-- Restricting a degree-zero form along `W' ≤ W` restricts the function it is equal to. -/
theorem incl_rO_of_eq {W W' : X.Opens} (h : W' ≤ W)
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((0 : ℕ) : ℤ)).val.obj (op (OO D M W))} {g : Γ(X, W ⊓ cU' D M)}
    (hg : (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) ω =
      sm ((cU D).ι ≫ f) (OO D M W) ((cU D).ι.app (W ⊓ cU' D M) g)) :
    (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) (rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h ω) =
      sm ((cU D).ι ≫ f) (OO D M W') ((cU D).ι.app (W' ⊓ cU' D M)
        (X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) h)).op g)) :=
  incl_map_eq_sm f D (inf_le_inf_right (cU' D M) h) hg

end Restrict

section Cond

variable (n : ℕ) {X T : Scheme.{u}} (f : X ⟶ T) [SmoothOfRelativeDimension n f]
  [IsLocallyNoetherian X] [IsNormal X] (D : Divisor X) (hD : D.IsRelativeSNC n f) (S M : Divisor X)

omit [SmoothOfRelativeDimension n f] [IsLocallyNoetherian X] [IsNormal X] in
/-- The open `U' = X ∖ (D ∪ Supp M)` is contained in `U = X ∖ D`. -/
theorem cU'_le_cU : cU' D M ≤ cU D := fun _ hx hxD => hx (Or.inl hxD)

/-- A degree-zero form satisfying `Cond` is a section of `𝒪_X(-M)`. -/
theorem divCond_of_cond_zero {W : X.Opens}
    {ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
      ((0 : ℕ) : ℤ)).val.obj (op (OO D M W))}
    (hω : Cond n f D hD S M 0 W ω) (g : Γ(X, W ⊓ cU' D M))
    (hg : (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ) ω =
      sm ((cU D).ι ≫ f) (OO D M W) ((cU D).ι.app (W ⊓ cU' D M) g)) :
    DivCond (D := D) (M := M) W g := by
  classical
  refine divCond_of_local fun y hy => ?_
  obtain ⟨W₁, h₁, hy₁, m, gs, η, hgs, hη, he⟩ := hω y hy
  choose W'' hle hy'' c hc hce using fun i =>
    B1.exists_res_of_mem_relativeLogForms_zero f D n hD S.suppIdeal (hη i) hy₁
  obtain ⟨W', hy', hW'₀, hW''⟩ := exists_affine_forall Finset.univ
    (fun i (Z : X.Opens) => Z ≤ W'' i) (fun _ _ _ h₁ h₂ => h₁.trans h₂)
    (fun i _ => ⟨W'' i, hy'' i, le_rfl⟩) (W₁ : X.Opens) hy₁
  have k₁ : (W' : X.Opens) ≤ W₁ := hW'₀
  have k'' : ∀ i, (W' : X.Opens) ≤ W'' i := fun i => hW'' i (Finset.mem_univ i)
  refine ⟨W', k₁.trans h₁, hy', ?_⟩
  have he₃ := (congrArg ((TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ))
    (rO_rO f (D := D) (M := M) ((0 : ℕ) : ℤ) h₁ k₁ ω)).symm.trans
      (sum_rep_restrict f D M k₁ gs η he)
  have hi : ∀ i, (TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        ((0 : ℕ) : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono (cU D).ι
          (inf_le_left.trans k₁))).op (η i)) =
      sm ((cU D).ι ≫ f) (OO D M W') (resO D M W' (X.presheaf.map (homOfLE (k'' i)).op (c i))) := by
    intro i
    have hψ : (W' : X.Opens) ⊓ cU' D M ≤ W'' i := inf_le_left.trans (k'' i)
    have e1 := congrArg ((TB ((cU D).ι ≫ f)).incl ((0 : ℕ) : ℤ))
      (piece_map_map _ ((Opens.map (cU D).ι.base).map (homOfLE (hle i))).op
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι hψ)).op
        (homOfLE (Scheme.Hom.preimage_mono (cU D).ι (inf_le_left.trans k₁))).op (η i))
    have e2 := incl_map f D (homOfLE (Scheme.Hom.preimage_mono (cU D).ι hψ)).op ((0 : ℕ) : ℤ)
      (((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).piece
        ((0 : ℕ) : ℤ)).val.map ((Opens.map (cU D).ι.base).map (homOfLE (hle i))).op (η i))
    refine (e1.symm.trans e2).trans ?_
    refine (congrArg _ (hce i)).trans ?_
    refine (totalRestrict_sm _ _).trans ?_
    exact congrArg _ ((G1.app_restrict hψ (c i)).trans
      (congrArg _ (presheaf_map_map _ _ _ _).symm))
  let G : Γ(X, (W' : X.Opens) ⊓ cU' D M) := ∑ i, X.presheaf.map
    (homOfLE (inf_le_inf_right _ k₁)).op (gs i) *
      X.presheaf.map (homOfLE inf_le_left).op (X.presheaf.map (homOfLE (k'' i)).op (c i))
  suffices heq : X.presheaf.map (homOfLE (inf_le_inf_right (cU' D M) (k₁.trans h₁))).op g = G by
    rw [heq]
    exact divCond_sum _ _ fun i _ => divCond_mul _ (DivCond.restrict D M k₁ (hgs i))
  apply (ι_app_bijective (cU D) _ (inf_le_right.trans (cU'_le_cU D M))).1
  apply sm_injective ((cU D).ι ≫ f) (OO D M W')
  refine (incl_rO_of_eq f D M (k₁.trans h₁) hg).symm.trans (he₃.trans ?_)
  refine (Finset.sum_congr rfl fun i _ => by rw [hi i]).trans ?_
  change ∑ i, sm ((cU D).ι ≫ f) (OO D M W') _ * _ = _
  simp only [← map_mul, ← map_sum]
  refine congrArg _ ?_
  simp only [G, map_sum, map_mul]

end Cond

section LogOne

variable (n : ℕ) {X T : Scheme.{u}} (f : X ⟶ T) [SmoothOfRelativeDimension n f]
  (D : Divisor X) (hD : D.IsRelativeSNC n f)

/-- The support ideal of the zero divisor is the unit ideal on every affine open. -/
theorem suppIdeal_zero_ideal (W : X.affineOpens) : (0 : Divisor X).suppIdeal.ideal W = ⊤ := by
  have : (0 : Divisor X).supp = ⊥ := by
    simp [DivisorWithCoeffs.supp]
  rw [DivisorWithCoeffs.suppIdeal, this, Scheme.IdealSheafData.vanishingIdeal_bot]
  rfl

/-- The unit is a section of `Ω^0_X(log D) = 𝒪_X`, with no condition along the empty divisor. -/
theorem one_mem_relativeLogForms_zero (W : X.Opens) :
    (TB ((cU D).ι ≫ f)).one.eval (op ((cU D).ι ⁻¹ᵁ W)) ∈
      Divisor.relativeLogForms n f D hD (0 : Divisor X).suppIdeal ((0 : ℕ) : ℤ) W := by
  refine (G1.mem_relativeLogForms_iff' n f D hD _ _ _ _).2 fun x hx => ?_
  obtain ⟨W', hxW', hle⟩ := G1.exists_affineOpens_le (X := X) hx
  refine ⟨W', hle, hxW', ?_⟩
  rw [G1.Br_iff]
  have h1 : G1.rs f D ((0 : ℕ) : ℤ) hle ((TB ((cU D).ι ≫ f)).one.eval (op ((cU D).ι ⁻¹ᵁ W))) =
      (TB ((cU D).ι ≫ f)).one.eval (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens))) :=
    (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ f)).one.2 _
  rw [h1]
  change (1 : (TB ((cU D).ι ≫ f)).Total (op ((cU D).ι ⁻¹ᵁ (W' : X.Opens)))) ∈ _
  refine AddSubgroup.subset_closure ⟨1, ?_, 1, Subring.one_mem _, ?_⟩
  · rw [suppIdeal_zero_ideal]
    exact Submodule.mem_top
  · rw [map_one]
    exact ((mul_one _).trans (map_one _)).symm

end LogOne

section Model

variable (n : ℕ) {V : Scheme.{0}} (π : V ⟶ Spec (CommRingCat.of ℂ))
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
  (D : Divisor V) (hD : D.IsRelativeSNC n π) (M : Divisor V) (N : ℕ) (u : Γ(V, cU' D M))
  {K : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}

variable {n π D hD M N u} in
/-- A degree-zero form lies in the image of `ι 0 W` if and only if it satisfies `Cond`. -/
theorem isCModel_range_iff_cond {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    (W : V.Opens) (ω) : ω ∈ Set.range (ι 0 W) ↔ Cond n π D hD S M 0 W ω :=
  hK.2.2.2.2.1 0 W ω

variable {n π D hD M N u} in
/-- The degree-zero embedding `ι 0 W` of a model is injective. -/
theorem isCModel_injective {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    (W : V.Opens) : Function.Injective (ι 0 W) :=
  hK.1 0 W

variable {n π D hD M N u} in
/-- The degree-zero embedding `ι 0 W` of a model is additive. -/
theorem isCModel_map_add {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    (W : V.Opens) (x y) : ι 0 W (x + y) = ι 0 W x + ι 0 W y :=
  hK.2.1 0 W x y

variable {n π D hD M N u} in
/-- The degree-zero embedding of a model is compatible with multiplication by functions. -/
theorem isCModel_incl_smul {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    (W : V.Opens) (r : V.ringCatSheaf.obj.obj (op W)) (x) :
    (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ) (ι 0 W (r • x)) =
      sm ((cU D).ι ≫ π) (OO D M W) (resO D M W r) *
        (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ) (ι 0 W x) :=
  hK.2.2.1 0 W r x

variable {n π D hD M N u} in
/-- The degree-zero embedding of a model commutes with restriction. -/
theorem isCModel_map_restrict {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)
    {W W' : V.Opens} (h : W' ≤ W) (x) :
    ι 0 W' ((F 0).val.map (homOfLE h).op x) = rO π (D := D) (M := M) ((0 : ℕ) : ℤ) h (ι 0 W x) :=
  hK.2.2.2.1 0 W W' h x

variable {n π D hD M N u} in
/-- `x` is represented by the rational function `a`: the degree-zero form `ι x` is a function `g`
on `W ∩ U'`, and `a` restricts to `g` there. -/
def DegreeZeroRep (ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
      ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
        (op (OO D M W)))
    (W : V.Opens) (x : (F 0).val.obj (op W))
    (a : ToType ((rationalFunctionsPresheaf V).obj (op W))) :
    Prop :=
  ∃ g : Γ(V, W ⊓ cU' D M),
    (rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a =
      (toRationalFunctionsPresheaf V).app (op (W ⊓ cU' D M)) g ∧
    (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ) (ι 0 W x) =
      sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app (W ⊓ cU' D M) g)

variable {n π D hD M N u} {S : Divisor V} (hK : IsCModel n π D hD S M N u K F e ι)

include hK

/-- Every section of `F 0` is represented by a section of `𝒪_V(-M)`. -/
theorem DegreeZeroRep.exists (W : V.Opens) (x : (F 0).val.obj (op W)) :
    ∃ a ∈ (-M).divisorialSubmodule W, DegreeZeroRep ι W x a := by
  obtain ⟨c, hc⟩ := exists_incl_zero_eq_sm ((cU D).ι ≫ π) (OO D M W) (ι 0 W x)
  obtain ⟨g, rfl⟩ := (ι_app_bijective (cU D) _ (inf_le_right.trans (cU'_le_cU D M))).2 c
  obtain ⟨a, ha, he⟩ :=
    divCond_of_cond_zero n π D hD S M ((isCModel_range_iff_cond hK W _).1 ⟨x, rfl⟩) g hc
  exact ⟨a, ha, g, he, hc⟩

omit hK [IsLocallyNoetherian V] [IsNormal V] in
/-- The rational function representing a section of `F 0` is unique. -/
theorem DegreeZeroRep.unique {W : V.Opens} {x : (F 0).val.obj (op W)}
    {a b : ToType ((rationalFunctionsPresheaf V).obj (op W))}
    (ha : DegreeZeroRep ι W x a) (hb : DegreeZeroRep ι W x b) : a = b := by
  obtain ⟨g, hga, hgx⟩ := ha
  obtain ⟨g', hgb, hgy⟩ := hb
  have hgg : g = g' := (ι_app_bijective (cU D) _ (inf_le_right.trans (cU'_le_cU D M))).1
    (sm_injective _ _ (hgx.symm.trans hgy))
  subst hgg
  exact rationalFunctionsPresheaf_map_inf_injective (componentGenericPoint_mem_cU' D M)
    (hga.trans hgb.symm)

/-- Two sections of `F 0` represented by the same rational function are equal. -/
theorem DegreeZeroRep.injective {W : V.Opens} {x y : (F 0).val.obj (op W)}
    {a : ToType ((rationalFunctionsPresheaf V).obj (op W))}
    (hx : DegreeZeroRep ι W x a) (hy : DegreeZeroRep ι W y a) : x = y := by
  obtain ⟨g, hga, hgx⟩ := hx
  obtain ⟨g', hgb, hgy⟩ := hy
  have hgg : g = g' := toRationalFunctionsPresheaf_app_injective _ (hga.symm.trans hgb)
  subst hgg
  exact isCModel_injective hK W (formsIncl_injective _ (OO D M W) _ (hgx.trans hgy.symm))

omit hK [IsLocallyNoetherian V] [IsNormal V] in
/-- If `x` is represented by `a` and `y` by `b`, then `x + y` is represented by `a + b`. -/
theorem DegreeZeroRep.add {W : V.Opens} {x y : (F 0).val.obj (op W)}
    {a b : ToType ((rationalFunctionsPresheaf V).obj (op W))}
    (hx : DegreeZeroRep ι W x a) (hy : DegreeZeroRep ι W y b)
    (hadd : ι 0 W (x + y) = ι 0 W x + ι 0 W y) :
    DegreeZeroRep ι W (x + y) (a + b) := by
  obtain ⟨g, hga, hgx⟩ := hx
  obtain ⟨g', hgb, hgy⟩ := hy
  refine ⟨g + g', by rw [map_add, hga, hgb, map_add], ?_⟩
  rw [hadd, Stacks.GradedAlgebra.incl_add, hgx, hgy, map_add, map_add]

/-- If `x` is represented by `a`, then `r • x` is represented by `r • a`. -/
theorem DegreeZeroRep.smul {W : V.Opens} {x : (F 0).val.obj (op W)}
    {a : ToType ((rationalFunctionsPresheaf V).obj (op W))} (r : Γ(V, W))
    (hx : DegreeZeroRep ι W x a) :
    DegreeZeroRep ι W ((show V.ringCatSheaf.obj.obj (op W) from r) • x) (r • a) := by
  obtain ⟨g, hga, hgx⟩ := hx
  refine ⟨V.presheaf.map (homOfLE inf_le_left).op r * g, ?_, ?_⟩
  · rw [rationalFunctionsPresheaf_map_smul, hga, Algebra.smul_def, map_mul]
    rfl
  · rw [isCModel_incl_smul hK, hgx, ← map_mul, map_mul ((cU D).ι.app (W ⊓ cU' D M)).hom]

/-- Representation is compatible with restriction to a smaller open. -/
theorem DegreeZeroRep.restrict {W W' : V.Opens} (h : W' ≤ W) {x : (F 0).val.obj (op W)}
    {a : ToType ((rationalFunctionsPresheaf V).obj (op W))}
    (hx : DegreeZeroRep ι W x a) :
    DegreeZeroRep ι W' ((F 0).val.map (homOfLE h).op x)
      ((rationalFunctionsPresheaf V).map (homOfLE h).op a) := by
  obtain ⟨g, hga, hgx⟩ := hx
  refine ⟨V.presheaf.map (homOfLE (inf_le_inf_right _ h)).op g, ?_, ?_⟩
  · rw [toRationalFunctionsPresheaf_app_map, ← hga]
    rfl
  · rw [isCModel_map_restrict hK]
    exact incl_rO_of_eq π D M h hgx

omit hK in
/-- For a model with `S = 0`, every section of `𝒪_V(-M)` represents a section of `F 0`. -/
theorem DegreeZeroRep.surjective (hK : IsCModel n π D hD 0 M N u K F e ι) {W : V.Opens}
    {a : ToType ((rationalFunctionsPresheaf V).obj (op W))}
    (ha : a ∈ (-M).divisorialSubmodule W) : ∃ x, DegreeZeroRep ι W x a := by
  have hdiv : (0 : Divisor V).IsDivisorialSection (W ⊓ cU' D M)
      ((rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op a) := by
    intro E hE
    have h1 := (Divisor.IsDivisorialSection.map (homOfLE inf_le_left) ha) E hE
    have hM0 : M E = 0 := coeff_eq_zero_of_meets
      (inf_le_right.trans (show cU' D M ≤ M.supp.compl from fun x hx hxM => hx (Or.inr hxM))) hE
    have h2 : (-M).coeff E = (0 : Divisor V).coeff E := by
      rw [DivisorWithCoeffs.coeff_neg, DivisorWithCoeffs.coeff_zero, DivisorWithCoeffs.coeff_apply,
        hM0, neg_zero]
    rwa [h2] at h1
  obtain ⟨g, hg⟩ := hdiv.exists_eq
  let ω : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
      ((0 : ℕ) : ℤ)).val.obj (op (OO D M W)) :=
    (show (Stacks.RingedSpace.structureRingSheaf (cU D).toScheme.toRingedSpace).obj.obj
      (op (OO D M W)) from (cU D).ι.app (W ⊓ cU' D M) g) •
      (TB ((cU D).ι ≫ π)).one.eval (op (OO D M W))
  have hω : (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ) ω =
      sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app (W ⊓ cU' D M) g) :=
    (sm_eq_incl_smul_one _ _ _).symm
  have hcond : Cond n π D hD 0 M 0 W ω := by
    intro y hy
    obtain ⟨W', hyW', hle⟩ := G1.exists_affineOpens_le (X := V) hy
    refine ⟨W', hle, hyW', 1, fun _ => V.presheaf.map (homOfLE (inf_le_inf_right _ hle)).op g,
      fun _ => (TB ((cU D).ι ≫ π)).one.eval (op ((cU D).ι ⁻¹ᵁ (W' : V.Opens))),
      fun _ => DivCond.restrict D M hle ⟨a, ha, hg.symm⟩,
      fun _ => one_mem_relativeLogForms_zero n π D hD _, ?_⟩
    rw [Fin.sum_univ_one]
    have h1 : ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
        ((0 : ℕ) : ℤ)).val.map (homOfLE (Scheme.Hom.preimage_mono _ inf_le_left)).op
          ((TB ((cU D).ι ≫ π)).one.eval (op ((cU D).ι ⁻¹ᵁ (W' : V.Opens)))) =
        (TB ((cU D).ι ≫ π)).one.eval (op (OO D M W')) :=
      (Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).one.2 _
    rw [h1]
    change _ = _ * (1 : (TB ((cU D).ι ≫ π)).Total (op (OO D M W')))
    rw [mul_one]
    exact incl_rO_of_eq π D M hle hω
  obtain ⟨x, hx⟩ := (isCModel_range_iff_cond hK W ω).2 hcond
  exact ⟨x, g, hg.symm, by rwa [hx]⟩

/-- The section of `𝒪_V(-M)` representing a section of `F 0`. -/
noncomputable def degreeZeroFun (W : V.Opens) (x : (F 0).val.obj (op W)) :
    (-M).divisorialSubmodule W :=
  ⟨(DegreeZeroRep.exists hK W x).choose, (DegreeZeroRep.exists hK W x).choose_spec.1⟩

/-- The section `degreeZeroFun hK W x` represents `x`. -/
theorem degreeZeroFun_rep (W : V.Opens) (x : (F 0).val.obj (op W)) :
    DegreeZeroRep ι W x (degreeZeroFun hK W x).1 :=
  (DegreeZeroRep.exists hK W x).choose_spec.2

/-- `degreeZeroFun` is additive. -/
theorem degreeZeroFun_add (W : V.Opens) (x y : (F 0).val.obj (op W)) :
    degreeZeroFun hK W (x + y) = degreeZeroFun hK W x + degreeZeroFun hK W y :=
  Subtype.ext (DegreeZeroRep.unique (degreeZeroFun_rep hK W (x + y))
    (DegreeZeroRep.add (degreeZeroFun_rep hK W x) (degreeZeroFun_rep hK W y)
      (isCModel_map_add hK W x y)))

/-- The morphism `F 0 ⟶ 𝒪_V(-M)` sending a section to the rational function it represents. -/
noncomputable def degreeZeroHom : F 0 ⟶ (-M).divisorialSheaf :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom (AddMonoidHom.mk' (degreeZeroFun hK U.unop)
        (degreeZeroFun_add hK U.unop))
      naturality U U' i := by
        ext x
        exact Subtype.ext (DegreeZeroRep.unique
          (degreeZeroFun_rep hK U'.unop ((F 0).val.map (homOfLE i.unop.le).op x))
          (DegreeZeroRep.restrict hK i.unop.le (degreeZeroFun_rep hK U.unop x))) }
    fun U r x => Subtype.ext (DegreeZeroRep.unique (degreeZeroFun_rep hK U.unop (r • x))
      (DegreeZeroRep.smul hK r (degreeZeroFun_rep hK U.unop x)))⟩

/-- The morphism `degreeZeroHom` sends a section to its `degreeZeroFun`. -/
@[simp] theorem degreeZeroHom_app (W : V.Opens) (x : (F 0).val.obj (op W)) :
    (degreeZeroHom hK).app W x = degreeZeroFun hK W x := rfl

omit hK in
/-- For a model with `S = 0`, the morphism `F 0 ⟶ 𝒪_V(-M)` is an isomorphism. -/
theorem isIso_degreeZeroHom (hK : IsCModel n π D hD 0 M N u K F e ι) :
    IsIso (degreeZeroHom hK) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y h => ?_, fun a => ?_⟩
  · change degreeZeroFun hK W x = degreeZeroFun hK W y at h
    refine DegreeZeroRep.injective hK (degreeZeroFun_rep hK W x) ?_
    rw [h]
    exact degreeZeroFun_rep hK W y
  · obtain ⟨x, hx⟩ := DegreeZeroRep.surjective hK a.2
    exact ⟨x, Subtype.ext (DegreeZeroRep.unique (degreeZeroFun_rep hK W x) hx)⟩

omit hK in
/-- **The degree-zero term of a model of `C^•` with `S = 0` is `𝒪_V(-M)`.** -/
noncomputable def degreeZeroIso (hK : IsCModel n π D hD 0 M N u K F e ι) :
    F 0 ≅ (-M).divisorialSheaf :=
  haveI := isIso_degreeZeroHom hK
  asIso (degreeZeroHom hK)

omit hK in
/-- The forward map of `degreeZeroIso` is `degreeZeroHom`. -/
@[simp] theorem degreeZeroIso_hom (hK : IsCModel n π D hD 0 M N u K F e ι) :
    (degreeZeroIso hK).hom = degreeZeroHom hK := rfl

omit hK in
/-- **The degree-zero term of a model, compatibly with the forms.** For a model `(K, F, e, ι)` of
`C^•` with `S = 0`, the isomorphism `F 0 ≅ 𝒪_V(-M)` sends a section `x` over `W` to the rational
function `a` such that `ι x` is the degree-zero form of a function `g` on `U ∩ W ∩ U'` whose
rational function is the restriction of `a`. -/
theorem degreeZeroIso_hom_app (hK : IsCModel n π D hD 0 M N u K F e ι) (W : V.Opens)
    (x : (F 0).val.obj (op W)) :
    ∃ g : Γ(V, W ⊓ cU' D M),
      (rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op
          ((degreeZeroIso hK).hom.app W x).1 =
        (toRationalFunctionsPresheaf V).app (op (W ⊓ cU' D M)) g ∧
      (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ) (ι 0 W x) =
        sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app (W ⊓ cU' D M) g) :=
  degreeZeroFun_rep hK W x

omit hK in
/-- **(a1) The degree-zero term of every model of `C^•` with `S = 0` is `𝒪_V(-M)`**,
compatibly with the embedding `ι` into the forms on `U ∩ W ∩ U'` and the embedding of `𝒪_V(-M)`
into the rational functions. -/
theorem exists_iso_divisorialSheaf_of_isCModel (hK : IsCModel n π D hD 0 M N u K F e ι) :
    ∃ Ψ : F 0 ≅ (-M).divisorialSheaf, ∀ (W : V.Opens) (x : (F 0).val.obj (op W)),
      ∃ g : Γ(V, W ⊓ cU' D M),
        (rationalFunctionsPresheaf V).map (homOfLE inf_le_left).op (Ψ.hom.app W x).1 =
          (toRationalFunctionsPresheaf V).app (op (W ⊓ cU' D M)) g ∧
        (TB ((cU D).ι ≫ π)).incl ((0 : ℕ) : ℤ) (ι 0 W x) =
          sm ((cU D).ι ≫ π) (OO D M W) ((cU D).ι.app (W ⊓ cU' D M) g) :=
  ⟨degreeZeroIso hK, degreeZeroIso_hom_app hK⟩

end Model

section Twist

variable {n : ℕ} {V : Scheme.{0}} {π : V ⟶ Spec (CommRingCat.of ℂ)}
  [SmoothOfRelativeDimension n π] [IsLocallyNoetherian V] [IsNormal V]
  {D : Divisor V} {hD : D.IsRelativeSNC n π} {M M' : Divisor V} {N N' : ℕ}
  {u : Γ(V, cU' D M)} {u' : Γ(V, cU' D M')}
  {K K' : CochainComplex (SheafOfModules.{0} (SheafOfModules.underlyingRingSheaf
    ((TopCat.Sheaf.pullback CommRingCat.{0} π.base).obj (Spec (CommRingCat.of ℂ)).sheaf))) ℕ}
  {F F' : ℕ → V.Modules}
  {e : ∀ p, K.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F p)}
  {e' : ∀ p, K'.X p ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (F' p)}
  {ι : ∀ (p : ℕ) (W : V.Opens), (F p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M W))}
  {ι' : ∀ (p : ℕ) (W : V.Opens), (F' p).val.obj (op W) →
    ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece (p : ℤ)).val.obj
      (op (OO D M' W))}

/-- Let `y` be a section of `F' 0` and `z` a section of `F 0` whose form `ι z` is the restriction
of `ι' y`. Then `z` is represented by the rational function `(degreeZeroIso hK').hom.app W y`. -/
theorem degreeZeroRep_of_twist (hK' : IsCModel n π D hD 0 M' N' u' K' F' e' ι')
    (hM : cU' D M' = cU' D M) {W : V.Opens} (y : (F' 0).val.obj (op W))
    (z : (F 0).val.obj (op W))
    (hz : ι 0 W z = ((Scheme.Hom.relativeDifferentialFormsAlgebra ((cU D).ι ≫ π)).piece
      ((0 : ℕ) : ℤ)).val.map
        (homOfLE (show OO D M W ≤ OO D M' W by simp only [OO, hM]; exact le_rfl)).op
        (ι' 0 W y)) :
    DegreeZeroRep ι W z ((degreeZeroIso hK').hom.app W y).1 := by
  obtain ⟨g', hga, hgy⟩ := degreeZeroIso_hom_app hK' W y
  have hWW : W ⊓ cU' D M ≤ W ⊓ cU' D M' := by rw [hM]
  refine ⟨V.presheaf.map (homOfLE hWW).op g', ?_, ?_⟩
  · rw [toRationalFunctionsPresheaf_app_map, ← hga]
    rfl
  · rw [hz]
    exact incl_map_eq_sm π D hWW hgy

/-- In degree zero, a morphism of models commuting with the embeddings into the forms is, on
sections, the inclusion `𝒪_V(-M') ⟶ 𝒪_V(-M)`. -/
theorem degreeZeroIso_hom_app_twist (hK : IsCModel n π D hD 0 M N u K F e ι)
    (hK' : IsCModel n π D hD 0 M' N' u' K' F' e' ι') (hM : cU' D M' = cU' D M)
    (hle : -M' ≤ -M) (φ : K' ⟶ K)
    (hφ : IsTwistInclusion π D M M' hM e e' ι ι' φ)
    (W : V.Opens) (x : (K'.X 0).val.obj (op W)) :
    (degreeZeroIso hK).hom.app W ((e 0).hom.val.app (op W) ((φ.f 0).val.app (op W) x)) =
      (Divisor.divisorialSheafInclusion hle).app W
        ((degreeZeroIso hK').hom.app W ((e' 0).hom.val.app (op W) x)) :=
  Subtype.ext (DegreeZeroRep.unique (degreeZeroIso_hom_app hK W _)
    (degreeZeroRep_of_twist hK' hM _ _ (hφ 0 W x)))

/-- **(a2) The twist inclusion in degree zero.** Let `K` be a model of `C^•` for `M` and `K'` one
for `M'`, both with `S = 0`, with the same open `U' = V ∖ (D ∪ Supp M) = V ∖ (D ∪ Supp M')`, and
`φ : K' ⟶ K` a morphism commuting with the embeddings into the forms. Under the isomorphisms
`F 0 ≅ 𝒪_V(-M)` and `F' 0 ≅ 𝒪_V(-M')`, the degree-zero component of `φ` is the inclusion
`𝒪_V(-M') ⟶ 𝒪_V(-M)`. -/
theorem degreeZeroIso_comp_twist (hK : IsCModel n π D hD 0 M N u K F e ι)
    (hK' : IsCModel n π D hD 0 M' N' u' K' F' e' ι') (hM : cU' D M' = cU' D M)
    (hle : -M' ≤ -M) (φ : K' ⟶ K)
    (hφ : IsTwistInclusion π D M M' hM e e' ι ι' φ) :
    φ.f 0 ≫ (e 0).hom = (e' 0).hom ≫
      (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).map
        ((degreeZeroIso hK').hom ≫ Divisor.divisorialSheafInclusion hle ≫
          (degreeZeroIso hK).inv) := by
  ext W x
  obtain ⟨W⟩ := W
  have key := degreeZeroIso_hom_app_twist hK hK' hM hle φ hφ W x
  have hinv := congrArg (fun f : F 0 ⟶ F 0 =>
    f.app W ((e 0).hom.val.app (op W) ((φ.f 0).val.app (op W) x))) (degreeZeroIso hK).hom_inv_id
  change _ = (degreeZeroIso hK).inv.app W ((Divisor.divisorialSheafInclusion hle).app W
    ((degreeZeroIso hK').hom.app W ((e' 0).hom.val.app (op W) x)))
  rw [← key]
  exact hinv.symm

/-- The degree-zero term of a model of `C^•` with `S = 0`, as a sheaf of `π⁻¹𝒪`-modules: the
isomorphism `e 0` followed by `F 0 ≅ 𝒪_V(-M)`. -/
noncomputable def degreeZeroRestrictIso (hK : IsCModel n π D hD 0 M N u K F e ι) :
    K.X 0 ≅ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
      (φ := AlgebraicGeometry.inverseImageStructureMap π))).obj (-M).divisorialSheaf :=
  e 0 ≪≫ (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
    (φ := AlgebraicGeometry.inverseImageStructureMap π))).mapIso (degreeZeroIso hK)

/-- **(a2), as sheaves of `π⁻¹𝒪`-modules.** Under `K.X 0 ≅ 𝒪_V(-M)` and `K'.X 0 ≅ 𝒪_V(-M')`, the
degree-zero component of a morphism `φ : K' ⟶ K` commuting with the embeddings into the forms is
the inclusion `𝒪_V(-M') ⟶ 𝒪_V(-M)`. -/
theorem degreeZeroRestrictIso_comp_twist (hK : IsCModel n π D hD 0 M N u K F e ι)
    (hK' : IsCModel n π D hD 0 M' N' u' K' F' e' ι') (hM : cU' D M' = cU' D M)
    (hle : -M' ≤ -M) (φ : K' ⟶ K)
    (hφ : IsTwistInclusion π D M M' hM e e' ι ι' φ) :
    φ.f 0 ≫ (degreeZeroRestrictIso hK).hom = (degreeZeroRestrictIso hK').hom ≫
      (SheafOfModules.restrictScalars (SheafOfModules.underlyingRingHom
        (φ := AlgebraicGeometry.inverseImageStructureMap π))).map
          (Divisor.divisorialSheafInclusion hle) := by
  ext W x
  obtain ⟨W⟩ := W
  exact degreeZeroIso_hom_app_twist hK hK' hM hle φ hφ W x

end Twist

end MMP.LcBpf
