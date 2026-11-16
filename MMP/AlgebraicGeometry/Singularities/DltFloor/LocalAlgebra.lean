module

public import MMP.AlgebraicGeometry.Singularities.CyclicCover.Basic
public import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.SeminormalLift
public import MMP.AlgebraicGeometry.Singularities.RelativeCanonical.Local
public import MMP.AlgebraicGeometry.Divisor.WeilSubsheaf.S2
public import MMP.RingTheory.PowerSeries.CompleteLocalRing
public import MMP.AlgebraicGeometry.Singularities.Semismooth.Normalization

/-!
# Commutative algebra for the floor of a dlt pair

Local commutative algebra used to show that the reduced floor `T = ⌊B⌋` of a projective dlt pair
`(X, B)` is a semi-dlt adjoint pair.

* At a point of a variety over a perfect field with regular local ring, the local ring is formally
  smooth and essentially of finite type, its residue field is formally smooth, and the
  differentials of a regular system of parameters together with lifts of a differential basis of
  the residue field form a basis of `Ω`.
* Seminormality: two seminormal branches meeting in a reduced scheme glue to a seminormal ring;
  regular local rings are seminormal; on a reduced `S₂` scheme seminormality of the rings of
  sections is detected at the points of codimension at most one.
* Completions: Cohen's structure theorem with coefficients in an algebraically closed field, the
  completion of a hypersurface quotient, and the completed local ring of a transversal crossing
  of two smooth branches, which is `k[[x₀, …, xₙ]] ⧸ (x₀x₁)`.
* Depth: in `0 → I → R → A → 0` with `R` and `I` Cohen–Macaulay, `A` is Cohen–Macaulay.

## Main results

* `MMP.Fourfold.SdltFloor.exists_basis_D_sumElim`
* `MMP.Fourfold.SdltFloor.isSeminormalRing_quotient_inf`
* `MMP.Fourfold.SdltFloor.isSeminormalRing_sections_of_satisfiesS2`
* `MMP.Fourfold.SdltFloor.hasCompletedLocalModel_of_ker_eq_span_mul`
* `MMP.Fourfold.SdltFloor.isCMModule_of_surjective_of_isCMModule_ker`

## References

* [H. Matsumura, *Commutative ring theory*][Matsumura1989]
* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], Section 5.1
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace MMP.Fourfold.SdltFloor

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

open MMP.Mori MMP.Flips MMP.Fourfold

section DifferentialBasis

open IsLocalRing KaehlerDifferential TensorProduct

/-- For a regular system of parameters `z` of `A` and `w` with residues of linearly independent
differentials in `Ω_{κ/R}`, the classes of `dz, dw` in `κ ⊗ Ω_{A/R}` are linearly independent. -/
public theorem linearIndependent_tmul_D_sumElim {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] [IsLocalRing A] [IsNoetherianRing A]
    [Algebra.FormallySmooth R A] [Algebra.FormallySmooth R (ResidueField A)] {d e : ℕ}
    {z : Fin d → A} (hz : MMP.Mori.IsRegularSystemOfParameters z) {w : Fin e → A}
    (hw : LinearIndependent (ResidueField A)
      fun l => D R (ResidueField A) (residue A (w l))) :
    LinearIndependent (ResidueField A)
      fun i => (1 : ResidueField A) ⊗ₜ[A] D R A (Sum.elim z w i) := by
  classical
  let κ := ResidueField A
  have hmap : ∀ a : A, KaehlerDifferential.mapBaseChange R A κ ((1 : κ) ⊗ₜ[A] D R A a) =
      D R κ (residue A a) := fun a => by
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]
    rfl
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  have hw0 : ∀ l, g (Sum.inr l) = 0 := by
    have h := congrArg (KaehlerDifferential.mapBaseChange R A κ) hg
    rw [map_sum, map_zero, Fintype.sum_sum_type] at h
    simp only [map_smul, Sum.elim_inl, Sum.elim_inr, hmap] at h
    have hz0 : ∀ j, D R κ (residue A (z j)) = 0 := fun j => by
      rw [(residue_eq_zero_iff _).mpr (hz.1 ▸ Ideal.subset_span ⟨j, rfl⟩), map_zero]
    simp only [hz0, smul_zero, Finset.sum_const_zero, zero_add] at h
    exact Fintype.linearIndependent_iff.mp hw _ h
  rcases i with i | l
  · choose a ha using fun j => residue_surjective (g (Sum.inl j))
    have hsum : ∑ j, a j • ((1 : κ) ⊗ₜ[A] D R A (z j)) = 0 := by
      rw [Fintype.sum_sum_type] at hg
      simp only [hw0, zero_smul, Finset.sum_const_zero, add_zero] at hg
      rw [← hg]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← ha j]
      exact (algebraMap_smul κ (a j) _).symm
    rw [← ha i]
    exact (residue_eq_zero_iff _).mpr
      (MMP.Intersection.mem_maximalIdeal_of_sum_smul_tmul_D_eq_zero hz a hsum i)
  · exact hw0 l

/-- **The differentials of coordinates at a smooth point form a basis.** Let `A` be a Noetherian
local ring, formally smooth and essentially of finite type over `R`, with residue field `κ`
formally smooth over `R`, and with `Ω_{A/R}` of rank `d + e`. For a regular system of parameters
`z₁, …, z_d` of `A` and `w₁, …, w_e ∈ A` whose residues have linearly independent differentials in
`Ω_{κ/R}`, the differentials `dz₁, …, dz_d, dw₁, …, dw_e` are a basis of `Ω_{A/R}`. -/
public theorem exists_basis_D_sumElim {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsLocalRing A] [IsNoetherianRing A]
    [Algebra.FormallySmooth R A] [Algebra.EssFiniteType R A]
    [Algebra.FormallySmooth R (ResidueField A)] {d e : ℕ}
    (hn : Module.finrank A Ω[A⁄R] = d + e)
    {z : Fin d → A} (hz : MMP.Mori.IsRegularSystemOfParameters z) {w : Fin e → A}
    (hw : LinearIndependent (ResidueField A)
      fun l => D R (ResidueField A) (residue A (w l))) :
    ∃ b : Module.Basis (Fin d ⊕ Fin e) A Ω[A⁄R],
      ⇑b = Sum.elim (fun i => D R A (z i)) (fun l => D R A (w l)) := by
  classical
  let κ := ResidueField A
  have : Module.Finite A Ω[A⁄R] := KaehlerDifferential.finite R A
  have : Module.Projective A Ω[A⁄R] := ((Algebra.formallySmooth_iff R A).mp inferInstance).1
  have : Module.Free A Ω[A⁄R] := Module.free_of_flat_of_isLocalRing
  let f : Fin d ⊕ Fin e → A := Sum.elim z w
  let v : Fin d ⊕ Fin e → κ ⊗[A] Ω[A⁄R] := fun i => (1 : κ) ⊗ₜ[A] D R A (f i)
  have hv : LinearIndependent κ v := linearIndependent_tmul_D_sumElim hz hw
  have hcard : Fintype.card (Fin d ⊕ Fin e) = Module.finrank κ (κ ⊗[A] Ω[A⁄R]) := by
    rw [Module.finrank_baseChange, hn, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  have hspanκ : Submodule.span κ (Set.range v) = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((finrank_span_eq_card hv).trans hcard)
  let bκ := Module.Basis.mk hv hspanκ.ge
  have hspan : Submodule.span A (Set.range fun i => D R A (f i)) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis _ bκ fun i => by
      simp only [bκ, v, Module.Basis.coe_mk]
  have hli : LinearIndependent A fun i => D R A (f i) :=
    linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge
      (by rw [hn, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin])
  refine ⟨Module.Basis.mk hli hspan.ge, ?_⟩
  rw [Module.Basis.coe_mk]
  funext i
  rcases i with i | l <;> rfl

end DifferentialBasis

section SmoothStalk

/-- At a point with regular local ring of a scheme locally of finite type over a perfect field,
the local ring is formally smooth and essentially of finite type over `k`. -/
public theorem formallySmooth_stalk {k : Type} [Field k] [PerfectField k] {X : Scheme.{0}}
    {sX : X ⟶ Spec (.of k)} [LocallyOfFiniteType sX] (x : X)
    (hreg : IsRegularLocalRing (X.presheaf.stalk x)) :
    letI := stalkAlgebra sX x
    Algebra.FormallySmooth k (X.presheaf.stalk x) ∧
      Algebra.EssFiniteType k (X.presheaf.stalk x) := by
  let := stalkAlgebra sX x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hU' : IsAffineOpen U := hU
  let x' : U := ⟨x, hxU⟩
  let := sectionAlgebra sX U
  have := finiteType_sectionAlgebra sX hU'
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf x'
  have := isScalarTower_section_stalk sX U x'
  have := hU'.isLocalization_stalk x'
  set q := (hU'.primeIdealOf x').asIdeal
  have := Algebra.isSeparableExtension_of_perfectField k q.ResidueField
  have hs : Algebra.IsSmoothAt k q :=
    (Algebra.isSmoothAt_iff_isRegularLocalRing q (X.presheaf.stalk x)).mpr hreg
  have : Algebra.EssFiniteType Γ(X, U) (X.presheaf.stalk x) := .of_isLocalization _ q.primeCompl
  refine ⟨?_, .comp k Γ(X, U) (X.presheaf.stalk x)⟩
  exact Algebra.FormallySmooth.of_equiv
    ((IsLocalization.algEquiv q.primeCompl (Localization.AtPrime q)
      (X.presheaf.stalk x)).restrictScalars k)

/-- The residue field of a local ring essentially of finite type over a perfect field is
formally smooth over it. -/
public theorem formallySmooth_residueField_stalk {k : Type} [Field k] [PerfectField k]
    {X : Scheme.{0}} {sX : X ⟶ Spec (.of k)} (x : X)
    (h : letI := stalkAlgebra sX x; Algebra.EssFiniteType k (X.presheaf.stalk x)) :
    letI := stalkAlgebra sX x
    Algebra.FormallySmooth k (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
  let := stalkAlgebra sX x
  have : Algebra.EssFiniteType (X.presheaf.stalk x)
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    (RingHom.essFiniteType_algebraMap).mp
      (RingHom.FiniteType.of_surjective (algebraMap (X.presheaf.stalk x)
        (IsLocalRing.ResidueField (X.presheaf.stalk x)))
        IsLocalRing.residue_surjective).essFiniteType
  have : Algebra.EssFiniteType k (IsLocalRing.ResidueField (X.presheaf.stalk x)) :=
    .comp _ (X.presheaf.stalk x) _
  exact Algebra.FormallySmooth.of_perfectField

/-- **Dimension formula.** On an irreducible scheme of dimension `n` locally of finite type over
`k`, `trdeg_k κ(x) + dim 𝒪_{X,x} = n`. -/
public theorem trdeg_residueField_stalk {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IrreducibleSpace X] [LocallyOfFiniteType sX] {n : ℕ}
    (hn : topologicalKrullDim X = n) (x : X) {d : ℕ}
    (hd : ringKrullDim (X.presheaf.stalk x) = d) :
    letI := stalkAlgebra sX x
    Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x)) = ((n - d : ℕ) : Cardinal) ∧
      d ≤ n := by
  let := stalkAlgebra sX x
  have h := topologicalKrullDimAt_eq_trdeg_add_krullDim_stalk k X sX x
  rw [← topologicalKrullDim_eq_topologicalKrullDimAt_of_irreducible k X sX x, hn, hd] at h
  have h' : (n : WithBot ℕ∞) = (Cardinal.toENat
      (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x))) : WithBot ℕ∞) + d := h
  generalize hT : Cardinal.toENat
      (Algebra.trdeg k (IsLocalRing.ResidueField (X.presheaf.stalk x))) = T at h'
  induction T using ENat.recTopCoe with
  | top =>
    have : (n : ℕ∞) = ⊤ + d := by exact_mod_cast h'
    simp at this
  | coe e =>
    have he : n = e + d := by exact_mod_cast h'
    refine ⟨?_, by omega⟩
    rw [show n - d = e by omega]
    exact Cardinal.toENat_eq_natCast.mp hT

end SmoothStalk

section Seminormal

/-- **Gluing two seminormal branches.** If `R ⧸ I` and `R ⧸ J` are seminormal and `R ⧸ (I ⊔ J)`
is reduced, then `R ⧸ (I ⊓ J)` is seminormal. -/
public theorem isSeminormalRing_quotient_inf {R : Type*} [CommRing R] (I J : Ideal R)
    (hI : IsSeminormalRing (R ⧸ I)) (hJ : IsSeminormalRing (R ⧸ J))
    (hIJ : IsReduced (R ⧸ (I ⊔ J))) : IsSeminormalRing (R ⧸ (I ⊓ J)) := by
  have hred : IsReduced (R ⧸ (I ⊓ J)) :=
    (Ideal.isRadical_iff_quotient_reduced _).mp
      (((Ideal.isRadical_iff_quotient_reduced I).mpr (seminormalRing_isReduced hI)).inf
        ((Ideal.isRadical_iff_quotient_reduced J).mpr (seminormalRing_isReduced hJ)))
  refine Stacks.RingTheory.Seminormal.isSeminormalRing_iff_exists.mpr fun x y hxy => ?_
  obtain ⟨X, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨Y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_pow, ← map_pow, Ideal.Quotient.eq, Ideal.mem_inf] at hxy
  have e : ∀ K : Ideal R, X ^ 3 - Y ^ 2 ∈ K →
      (Ideal.Quotient.mk K X) ^ 3 = (Ideal.Quotient.mk K Y) ^ 2 := fun K h => by
    rwa [← map_pow, ← map_pow, Ideal.Quotient.eq]
  obtain ⟨a1, ha1, -⟩ := hI _ _ (e I hxy.1)
  obtain ⟨a2, ha2, -⟩ := hJ _ _ (e J hxy.2)
  obtain ⟨α1, rfl⟩ := Ideal.Quotient.mk_surjective a1
  obtain ⟨α2, rfl⟩ := Ideal.Quotient.mk_surjective a2
  simp only [← map_pow, Ideal.Quotient.eq] at ha1 ha2
  have hsup : α1 - α2 ∈ I ⊔ J := by
    rw [← Ideal.Quotient.eq]
    apply Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq
    · rw [← map_pow, ← map_pow, Ideal.Quotient.eq,
        show α1 ^ 2 - α2 ^ 2 = (X - α2 ^ 2) - (X - α1 ^ 2) by ring]
      exact Submodule.sub_mem _ (Ideal.mem_sup_right ha2.1) (Ideal.mem_sup_left ha1.1)
    · rw [← map_pow, ← map_pow, Ideal.Quotient.eq,
        show α1 ^ 3 - α2 ^ 3 = (Y - α2 ^ 3) - (Y - α1 ^ 3) by ring]
      exact Submodule.sub_mem _ (Ideal.mem_sup_right ha2.2) (Ideal.mem_sup_left ha1.2)
  obtain ⟨i, hi, j, hj, hij⟩ := Submodule.mem_sup.mp hsup
  have e2 : α1 - i = α2 + j := by linear_combination -hij
  refine ⟨Ideal.Quotient.mk _ (α1 - i), ?_, ?_⟩ <;>
    rw [← map_pow, Ideal.Quotient.eq, Ideal.mem_inf] <;> constructor
  · rw [show X - (α1 - i) ^ 2 = (X - α1 ^ 2) - i * (i - 2 * α1) by ring]
    exact I.sub_mem ha1.1 (I.mul_mem_right _ hi)
  · rw [e2, show X - (α2 + j) ^ 2 = (X - α2 ^ 2) - j * (j + 2 * α2) by ring]
    exact J.sub_mem ha2.1 (J.mul_mem_right _ hj)
  · rw [show Y - (α1 - i) ^ 3 = (Y - α1 ^ 3) - i * (-3 * α1 ^ 2 + 3 * α1 * i - i ^ 2) by ring]
    exact I.sub_mem ha1.2 (I.mul_mem_right _ hi)
  · rw [e2, show Y - (α2 + j) ^ 3 = (Y - α2 ^ 3) - j * (3 * α2 ^ 2 + 3 * α2 * j + j ^ 2) by ring]
    exact J.sub_mem ha2.2 (J.mul_mem_right _ hj)

/-- A regular local ring is seminormal. -/
public theorem isSeminormalRing_of_isRegularLocalRing (R : Type*) [CommRing R]
    [IsRegularLocalRing R] : IsSeminormalRing R := by
  have := IsRegularLocalRing.isDomain R
  have := isIntegrallyClosed_of_isRegularLocalRing R
  exact _root_.isSeminormalRing_of_isIntegrallyClosed R

/-- A common square and cube root at `z` of the germs of two sections on `V` comes from a section
on a neighbourhood `U ≤ V` of `z` whose germs are such roots at every point of `U`. -/
public theorem exists_sq_cube_eq_germ_of_stalk {X : Scheme.{0}} {V : X.Opens} {x y : Γ(X, V)}
    {z : X} (hzV : z ∈ V) {c : X.presheaf.stalk z} (hc2 : X.presheaf.germ V z hzV x = c ^ 2)
    (hc3 : X.presheaf.germ V z hzV y = c ^ 3) :
    ∃ (U : X.Opens) (_ : z ∈ U) (hUV : U ≤ V) (a : Γ(X, U)), ∀ w (hw : w ∈ U),
      (X.presheaf.germ U w hw a) ^ 2 = X.presheaf.germ V w (hUV hw) x ∧
        (X.presheaf.germ U w hw a) ^ 3 = X.presheaf.germ V w (hUV hw) y := by
  obtain ⟨U₁, hzU₁, s, hs⟩ := X.presheaf.exists_germ_eq c
  obtain ⟨W₁, hzW₁, i₁, j₁, h₁⟩ := X.presheaf.germ_eq z hzU₁ hzV (s ^ 2) x
    (by rw [map_pow, hs, hc2])
  obtain ⟨W₂, hzW₂, i₂, j₂, h₂⟩ := X.presheaf.germ_eq z hzU₁ hzV (s ^ 3) y
    (by rw [map_pow, hs, hc3])
  refine ⟨W₁ ⊓ W₂, ⟨hzW₁, hzW₂⟩, inf_le_left.trans j₁.le,
    X.presheaf.map (homOfLE (inf_le_left.trans i₁.le)).op s, fun w hw => ⟨?_, ?_⟩⟩
  · have e := congrArg (X.presheaf.germ W₁ w hw.1) h₁
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at e
    rw [TopCat.Presheaf.germ_res_apply, ← map_pow, e]
  · have e := congrArg (X.presheaf.germ W₂ w hw.2) h₂
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at e
    rw [TopCat.Presheaf.germ_res_apply, ← map_pow, e]

/-- If restriction from `V` to `W ≤ V` is bijective, a section on `W` whose germs are square and
cube roots of those of `x, y` is the restriction of a common square and cube root of `x, y`. -/
public theorem exists_sq_cube_eq_of_bijective_map {X : Scheme.{0}} {W V : X.Opens} (hWV : W ≤ V)
    (hbij : Function.Bijective (X.presheaf.map (homOfLE hWV).op)) {x y : Γ(X, V)} {b : Γ(X, W)}
    (hbx : ∀ w (hw : w ∈ W), (X.presheaf.germ W w hw b) ^ 2 = X.presheaf.germ V w (hWV hw) x ∧
      (X.presheaf.germ W w hw b) ^ 3 = X.presheaf.germ V w (hWV hw) y) :
    ∃ c : Γ(X, V), c ^ 2 = x ∧ c ^ 3 = y := by
  obtain ⟨c, hc⟩ := hbij.2 b
  have hres : ∀ s t : Γ(X, V), (∀ w (hw : w ∈ W),
      X.presheaf.germ V w (hWV hw) s = X.presheaf.germ V w (hWV hw) t) → s = t := by
    intro s t hst
    apply hbij.1
    apply TopCat.Presheaf.section_ext X.sheaf
    intro w hw
    change X.presheaf.germ _ w hw _ = X.presheaf.germ _ w hw _
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact hst w hw
  have hcg : ∀ w (hw : w ∈ W), X.presheaf.germ V w (hWV hw) c = X.presheaf.germ W w hw b := by
    intro w hw
    rw [← hc, TopCat.Presheaf.germ_res_apply]
  refine ⟨c, hres _ _ fun w hw => ?_, hres _ _ fun w hw => ?_⟩
  · rw [map_pow, hcg w hw, (hbx w hw).1]
  · rw [map_pow, hcg w hw, (hbx w hw).2]

/-- **Seminormality on an `S₂` scheme is detected in codimension at most one.** On a reduced
locally Noetherian `S₂` scheme whose local rings of dimension at most one are seminormal, the
ring of sections over every open is seminormal. -/
public theorem isSeminormalRing_sections_of_satisfiesS2 {X : Scheme.{0}} [IsReduced X]
    [IsLocallyNoetherian X] (hX : MMP.Flips.SatisfiesS2 X)
    (h : ∀ x : X, ¬ 2 ≤ ringKrullDim (X.presheaf.stalk x) →
      IsSeminormalRing (X.presheaf.stalk x))
    (V : X.Opens) : IsSeminormalRing Γ(X, V) := by
  classical
  refine Stacks.RingTheory.Seminormal.isSeminormalRing_iff_exists.mpr fun x y hxy => ?_
  have hloc : ∀ z : {z : X // z ∈ V ∧ ¬ 2 ≤ ringKrullDim (X.presheaf.stalk z)},
      ∃ (U : X.Opens) (_ : z.1 ∈ U) (hUV : U ≤ V) (a : Γ(X, U)), ∀ w (hw : w ∈ U),
        (X.presheaf.germ U w hw a) ^ 2 = X.presheaf.germ V w (hUV hw) x ∧
          (X.presheaf.germ U w hw a) ^ 3 = X.presheaf.germ V w (hUV hw) y := by
    rintro ⟨z, hzV, hz⟩
    obtain ⟨c, ⟨hc2, hc3⟩, -⟩ := h z hz (X.presheaf.germ V z hzV x)
      (X.presheaf.germ V z hzV y) (by rw [← map_pow, ← map_pow, hxy])
    exact exists_sq_cube_eq_germ_of_stalk hzV hc2 hc3
  choose U hzU hUV a ha using hloc
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 U a := by
    intro p q
    apply TopCat.Presheaf.section_ext X.sheaf
    intro w hw
    change X.presheaf.germ _ w hw
        (X.presheaf.map (TopologicalSpace.Opens.infLELeft (U p) (U q)).op (a p)) =
      X.presheaf.germ _ w hw
        (X.presheaf.map (TopologicalSpace.Opens.infLERight (U p) (U q)).op (a q))
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
    exact Stacks.RingTheory.Seminormal.eq_of_sq_eq_of_cube_eq
      ((ha p w hw.1).1.trans (ha q w hw.2).1.symm) ((ha p w hw.1).2.trans (ha q w hw.2).2.symm)
  obtain ⟨b, hb, -⟩ := TopCat.Sheaf.existsUnique_gluing X.sheaf U a hcompat
  have hWV : iSup U ≤ V := iSup_le hUV
  have hbx : ∀ w (hw : w ∈ iSup U), (X.presheaf.germ (iSup U) w hw b) ^ 2 =
      X.presheaf.germ V w (hWV hw) x ∧ (X.presheaf.germ (iSup U) w hw b) ^ 3 =
      X.presheaf.germ V w (hWV hw) y := by
    intro w hw
    obtain ⟨p, hp⟩ := TopologicalSpace.Opens.mem_iSup.mp hw
    have e : X.presheaf.germ (iSup U) w hw b = X.presheaf.germ (U p) w hp (a p) := by
      rw [← hb p]
      exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
    rw [e]
    exact ha p w hp
  obtain ⟨c, hc2, hc3⟩ := exists_sq_cube_eq_of_bijective_map hWV
    (MMP.Flips.bijective_presheaf_map_of_satisfiesS2 hX hWV fun z hzV hzW => by
      by_contra hz
      exact hzW (TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨z, hzV, hz⟩, hzU _⟩)) hbx
  exact ⟨c, hc2.symm, hc3.symm⟩

end Seminormal

section Completion

open IsLocalRing

/-- An ideal of `R` containing a power of `I` is cut out of the `I`-adic completion by its
extension. -/
private theorem comap_map_algebraMap_adicCompletion {R : Type*} [CommRing R] (I J : Ideal R)
    {n : ℕ} (hJ : I ^ n ≤ J) :
    (J.map (algebraMap R (AdicCompletion I R))).comap (algebraMap R (AdicCompletion I R)) = J := by
  refine le_antisymm (fun x hx => ?_) Ideal.le_comap_map
  have h1 : Ideal.map (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)
      (J.map (algebraMap R (AdicCompletion I R))) = J.map (Ideal.Quotient.mk (I ^ n)) := by
    rw [Ideal.map_map]
    congr 1
  have h2 : Ideal.Quotient.mk (I ^ n) x ∈ J.map (Ideal.Quotient.mk (I ^ n)) := by
    rw [← h1]
    have := Ideal.mem_map_of_mem (AdicCompletion.evalₐ I n : AdicCompletion I R →+* R ⧸ I ^ n)
      (Ideal.mem_comap.mp hx)
    simpa [AdicCompletion.evalₐ_of] using this
  have h3 := Ideal.mem_comap.mpr h2
  rw [Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker] at h3
  exact (sup_le le_rfl hJ) h3

/-- Every element of the `I`-adic completion is congruent to an element of `R` modulo the `n`-th
power of the extended ideal. -/
private theorem exists_algebraMap_sub_mem_pow {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (x : AdicCompletion I R) :
    ∃ r : R, x - algebraMap R _ r ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  refine ⟨r, ?_⟩
  have hev : AdicCompletion.evalₐ I n (x - algebraMap R _ r) = 0 := by
    rw [map_sub, ← hr]
    simp
  have hker : x - algebraMap R _ r ∈ (AdicCompletion.eval I R n).ker := by
    rw [LinearMap.mem_ker,
      ← AdicCompletion.factor_evalₐ_eq_eval I _ (le_of_eq (Ideal.mul_top _).symm), hev, map_zero]
  rw [← AdicCompletion.pow_smul_top_eq_ker_eval hI, Ideal.smul_top_eq_map] at hker
  rwa [← Ideal.map_pow]

/-- The transition map `S ⧸ Iⁿ → S ⧸ Iᵐ` commutes with evaluating an element of the `I`-adic
completion. -/
private theorem factorₐ_evalₐ {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (I : Ideal S) {m n : ℕ} (hmn : m ≤ n) (x : AdicCompletion I S) :
    Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn : I ^ n ≤ I ^ m)
      (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨a, rfl⟩ := AdicCompletion.mk_surjective I S x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change (Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn)) _ = _
  rw [Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn a

/-- A family of `R`-algebra isomorphisms `P ⧸ Jⁿ ≃ₐ[R] S ⧸ Iⁿ` compatible with the transition
maps of the two towers of quotients assembles into an `R`-algebra isomorphism of the `J`-adic and
the `I`-adic completion. -/
private theorem exists_algEquiv_adicCompletion_of_quotientPow
    {R P S : Type*} [CommRing R] [CommRing P] [CommRing S] [Algebra R P] [Algebra R S]
    (J : Ideal P) (I : Ideal S)
    (e : ∀ n, (P ⧸ J ^ n) ≃ₐ[R] (S ⧸ I ^ n))
    (hcompat : ∀ {m n : ℕ} (hmn : m ≤ n),
        (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp (e n).toAlgHom
        = (e m).toAlgHom.comp (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn))) :
    ∃ F : AdicCompletion J P ≃ₐ[R] AdicCompletion I S,
      ∀ n x, AdicCompletion.evalₐ I n (F x) = e n (AdicCompletion.evalₐ J n x) := by
  have hF : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
          ((e n).toAlgHom.comp ((AdicCompletion.evalₐ J n).restrictScalars R))
      = (e m).toAlgHom.comp ((AdicCompletion.evalₐ J m).restrictScalars R) := by
    intro m n hmn
    ext x
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom]
    have h1 := AlgHom.congr_fun (hcompat hmn) ((AdicCompletion.evalₐ J n) x)
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom] at h1
    rw [h1]
    exact congrArg (e m) (factorₐ_evalₐ (R := R) J hmn x)
  let F : AdicCompletion J P →ₐ[R] AdicCompletion I S :=
    AdicCompletion.liftAlgHom I
      (fun n => (e n).toAlgHom.comp ((AdicCompletion.evalₐ J n).restrictScalars R)) hF
  have hG : ∀ {m n : ℕ} (hmn : m ≤ n),
      (Ideal.Quotient.factorₐ R (Ideal.pow_le_pow_right hmn)).comp
          ((e n).symm.toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars R))
      = (e m).symm.toAlgHom.comp ((AdicCompletion.evalₐ I m).restrictScalars R) := by
    intro m n hmn
    ext x
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom]
    have h1 := AlgHom.congr_fun (hcompat hmn) ((e n).symm ((AdicCompletion.evalₐ I n) x))
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] at h1
    rw [factorₐ_evalₐ (R := R) I hmn x] at h1
    apply (e m).injective
    rw [AlgEquiv.apply_symm_apply, ← h1]
  let G : AdicCompletion I S →ₐ[R] AdicCompletion J P :=
    AdicCompletion.liftAlgHom J
      (fun n => (e n).symm.toAlgHom.comp ((AdicCompletion.evalₐ I n).restrictScalars R)) hG
  refine ⟨AlgEquiv.ofAlgHom F G (AlgHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_)
    (AlgHom.ext fun x => AdicCompletion.ext_evalₐ fun n => ?_), fun n x => ?_⟩ <;>
  simp only [F, G, AlgHom.comp_apply, AlgHom.id_apply, AlgEquiv.ofAlgHom_apply,
    AdicCompletion.evalₐ_liftAlgHom, AlgHom.restrictScalars_apply, AlgEquiv.coe_toAlgHom,
    AlgEquiv.apply_symm_apply, AlgEquiv.symm_apply_apply]

/-- If `φ : R → A` is a surjection of local rings with kernel `(f)`, then the kernel of
`R → A ⧸ 𝔪_Aⁿ` is `𝔪_Rⁿ + (f)`. -/
private theorem ker_comp_mkₐ_pow_maximalIdeal {k R A : Type*} [CommRing k]
    [CommRing R] [IsLocalRing R] [Algebra k R] [CommRing A] [IsLocalRing A] [Algebra k A]
    (φ : R →ₐ[k] A) (hφ : Function.Surjective φ) {f : R}
    (hker : RingHom.ker φ = Ideal.span {f}) (n : ℕ) :
    RingHom.ker ((Ideal.Quotient.mkₐ k (maximalIdeal A ^ n)).comp φ) =
      maximalIdeal R ^ n ⊔ Ideal.span {f} := by
  ext x
  rw [RingHom.mem_ker]
  change Ideal.Quotient.mk _ (φ x) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, ← map_maximalIdeal_of_surjective (φ : R →+* A) hφ,
    ← Ideal.map_pow]
  change x ∈ Ideal.comap (φ : R →+* A) (Ideal.map (φ : R →+* A) (maximalIdeal R ^ n)) ↔ _
  rw [Ideal.comap_map_of_surjective' (φ : R →+* A) hφ,
    show RingHom.ker (φ : R →+* A) = RingHom.ker φ from rfl, hker]

/-- Two surjective `k`-algebra maps out of `R` with the same kernel differ by an isomorphism of
their targets. -/
private theorem exists_algEquiv_apply_eq_of_ker_eq {k R B C : Type*} [CommRing k] [CommRing R]
    [CommRing B] [CommRing C] [Algebra k R] [Algebra k B] [Algebra k C] (χ : R →ₐ[k] B)
    (ψ : R →ₐ[k] C) (hχ : Function.Surjective χ) (hψ : Function.Surjective ψ)
    (hker : RingHom.ker χ = RingHom.ker ψ) : ∃ e : B ≃ₐ[k] C, ∀ r, e (χ r) = ψ r := by
  refine ⟨(Ideal.quotientKerAlgEquivOfSurjective hχ).symm.trans
    ((Ideal.quotientEquivAlgOfEq k hker).trans (Ideal.quotientKerAlgEquivOfSurjective hψ)),
    fun r => ?_⟩
  have h1 : (Ideal.quotientKerAlgEquivOfSurjective hχ).symm (χ r) = Ideal.Quotient.mk _ r := by
    rw [AlgEquiv.symm_apply_eq]
    rfl
  change Ideal.quotientKerAlgEquivOfSurjective hψ (Ideal.quotientEquivAlgOfEq k hker
    ((Ideal.quotientKerAlgEquivOfSurjective hχ).symm (χ r))) = _
  rw [h1]
  rfl

/-- If `f` lies in the maximal ideal of `R`, then `R̂ ⧸ (f)` is a local ring. -/
private theorem isLocalRing_quotient_span_algebraMap {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {f : R} (hf : f ∈ maximalIdeal R) :
    IsLocalRing (AdicCompletion (maximalIdeal R) R ⧸
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) f}) := by
  have hK : Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) f} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top (by
      rw [Ideal.span_le, Set.singleton_subset_iff, AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem _ hf)
  have := Ideal.Quotient.nontrivial_iff.mpr hK
  exact IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective

/-- **The truncations of `R̂ ⧸ (f)`.** The map `R → (R̂ ⧸ (f)) ⧸ 𝔪ⁿ` is surjective with kernel
`𝔪ⁿ + (f)`. -/
private theorem ker_eq_and_surjective_quotient_adicCompletion {k R : Type*} [CommRing k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R] (f : R)
    (K : Ideal (AdicCompletion (maximalIdeal R) R))
    (hK : K = Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) f})
    [IsLocalRing (AdicCompletion (maximalIdeal R) R ⧸ K)] (n : ℕ)
    (ψ : R →ₐ[k] (AdicCompletion (maximalIdeal R) R ⧸ K) ⧸
      maximalIdeal (AdicCompletion (maximalIdeal R) R ⧸ K) ^ n)
    (hψ : ψ = (Ideal.Quotient.mkₐ k _).comp ((Ideal.Quotient.mkₐ k K).comp
      (IsScalarTower.toAlgHom k R (AdicCompletion (maximalIdeal R) R)))) :
    RingHom.ker ψ = maximalIdeal R ^ n ⊔ Ideal.span {f} ∧ Function.Surjective ψ := by
  subst hψ
  let ι' := algebraMap R (AdicCompletion (maximalIdeal R) R)
  let π := Ideal.Quotient.mk K
  have hmhat : maximalIdeal (AdicCompletion (maximalIdeal R) R) = (maximalIdeal R).map ι' :=
    AdicCompletion.maximalIdeal_eq_map
  have hmC : maximalIdeal (AdicCompletion (maximalIdeal R) R ⧸ K) =
      (maximalIdeal (AdicCompletion (maximalIdeal R) R)).map π :=
    (map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective).symm
  refine ⟨?_, fun w => ?_⟩
  · ext x
    rw [RingHom.mem_ker]
    change Ideal.Quotient.mk _ (π (ι' x)) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, hmC, ← Ideal.map_pow, ← Ideal.mem_comap,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, hmhat,
      ← Ideal.map_pow]
    have hKe : K = (Ideal.span {f}).map ι' := by rw [hK, Ideal.map_span, Set.image_singleton]
    rw [hKe, ← Ideal.map_sup, ← Ideal.mem_comap,
      comap_map_algebraMap_adicCompletion _ _ (le_sup_left : maximalIdeal R ^ n ≤ _)]
  · obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective c
    obtain ⟨r, hr⟩ := exists_algebraMap_sub_mem_pow (maximalIdeal R)
      (IsNoetherian.noetherian _) n x
    refine ⟨r, ?_⟩
    change Ideal.Quotient.mk _ (π (ι' r)) = Ideal.Quotient.mk _ (π x)
    rw [Ideal.Quotient.eq, ← map_sub, hmC, ← Ideal.map_pow]
    refine Ideal.mem_map_of_mem _ ?_
    rw [hmhat, ← neg_sub, Ideal.neg_mem_iff]
    exact hr

/-- If `φ : R → A` is a surjection of local `k`-algebras with kernel `(f)`, then
`Â ≃ R̂ ⧸ (f)` as `k`-algebras: both sides have the truncations `R ⧸ (𝔪ⁿ + (f))`, and `R̂ ⧸ (f)`
is complete. -/
private theorem nonempty_algEquiv_adicCompletion_quotient_span {k R A : Type*} [CommRing k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    [CommRing A] [IsLocalRing A] [Algebra k A]
    [IsNoetherianRing (AdicCompletion (maximalIdeal R) R)]
    (φ : R →ₐ[k] A) (hφ : Function.Surjective φ) {f : R}
    (hker : RingHom.ker φ = Ideal.span {f}) :
    Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k] AdicCompletion (maximalIdeal R) R ⧸
      Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) f}) := by
  classical
  let K : Ideal (AdicCompletion (maximalIdeal R) R) :=
    Ideal.span {algebraMap R (AdicCompletion (maximalIdeal R) R) f}
  have : IsLocalRing (AdicCompletion (maximalIdeal R) R ⧸ K) :=
    isLocalRing_quotient_span_algebraMap
      (le_maximalIdeal (RingHom.ker_ne_top φ) (hker ▸ Ideal.mem_span_singleton_self f))
  have hC : IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal R) R ⧸ K))
      (AdicCompletion (maximalIdeal R) R ⧸ K) := by
    have h := Rig.isAdicComplete_quotient (maximalIdeal (AdicCompletion (maximalIdeal R) R)) K
    rwa [map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective] at h
  let χ : ∀ n : ℕ, R →ₐ[k] A ⧸ maximalIdeal A ^ n := fun n => (Ideal.Quotient.mkₐ k _).comp φ
  let ψ : ∀ n : ℕ, R →ₐ[k] (AdicCompletion (maximalIdeal R) R ⧸ K) ⧸
      maximalIdeal (AdicCompletion (maximalIdeal R) R ⧸ K) ^ n := fun n =>
    (Ideal.Quotient.mkₐ k _).comp ((Ideal.Quotient.mkₐ k K).comp
      (IsScalarTower.toAlgHom k R (AdicCompletion (maximalIdeal R) R)))
  have hχs : ∀ n, Function.Surjective (χ n) := fun n =>
    Ideal.Quotient.mk_surjective.comp hφ
  have hψ : ∀ n, RingHom.ker (ψ n) = maximalIdeal R ^ n ⊔ Ideal.span {f} ∧
      Function.Surjective (ψ n) := fun n =>
    ker_eq_and_surjective_quotient_adicCompletion f K rfl n (ψ n) rfl
  choose e he using fun n => exists_algEquiv_apply_eq_of_ker_eq (χ n) (ψ n) (hχs n) (hψ n).2
    ((ker_comp_mkₐ_pow_maximalIdeal φ hφ hker n).trans (hψ n).1.symm)
  have hcompat : ∀ {a b : ℕ} (hab : a ≤ b),
      (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hab)).comp (e b).toAlgHom =
        (e a).toAlgHom.comp (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hab)) := by
    intro a b hab
    refine AlgHom.ext fun w => ?_
    obtain ⟨r, rfl⟩ := hχs b w
    change Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hab) (e b (χ b r)) =
      e a (Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hab) (χ b r))
    rw [he b r, show Ideal.Quotient.factorₐ k (Ideal.pow_le_pow_right hab) (χ b r) = χ a r from rfl,
      he a r]
    rfl
  obtain ⟨F, -⟩ := exists_algEquiv_adicCompletion_of_quotientPow (maximalIdeal A)
    (maximalIdeal (AdicCompletion (maximalIdeal R) R ⧸ K)) e hcompat
  exact ⟨F.trans ((AdicCompletion.ofAlgEquiv
    (maximalIdeal (AdicCompletion (maximalIdeal R) R ⧸ K))).restrictScalars k).symm⟩

/-- **The completion of a hypersurface quotient.** Let `φ : R → A` be a surjection of local
`k`-algebras with `R` Noetherian and `ker φ = (f)`, and `G : k[[t]] ≃ R̂` an isomorphism with
`G(g) = f`. Then `Â ≃ k[[t]] ⧸ (g)` as `k`-algebras: both sides have the truncations
`R ⧸ (𝔪ⁿ + (f))`, and `R̂ ⧸ (f)` is complete. -/
private theorem nonempty_algEquiv_adicCompletion_of_surjective {k R A : Type*} [Field k]
    [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    [CommRing A] [IsLocalRing A] [Algebra k A]
    (φ : R →ₐ[k] A) (hφ : Function.Surjective φ) {m : ℕ}
    (G : MvPowerSeries (Fin m) k ≃ₐ[k] AdicCompletion (maximalIdeal R) R)
    (g : MvPowerSeries (Fin m) k) (f : R)
    (hf : G g = algebraMap R (AdicCompletion (maximalIdeal R) R) f)
    (hker : RingHom.ker φ = Ideal.span {f}) :
    Nonempty (AdicCompletion (maximalIdeal A) A ≃ₐ[k]
      MvPowerSeries (Fin m) k ⧸ Ideal.span {g}) := by
  have : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    isNoetherianRing_of_ringEquiv _ G.toRingEquiv
  obtain ⟨F⟩ := nonempty_algEquiv_adicCompletion_quotient_span φ hφ hker
  refine ⟨F.trans (Ideal.quotientEquivAlg _ (Ideal.span {g}) G.symm ?_)⟩
  rw [Ideal.map_span, Set.image_singleton]
  congr 2
  rw [← hf]
  exact (G.symm_apply_apply g).symm

/-- **Cohen's structure theorem with coefficients in `k`.** Let `R` be a Noetherian local
`k`-algebra over an algebraically closed field `k` with residue field finite over `k`, and `z` a
regular system of parameters of `R`. Then `k[[t₁, …, tₘ]] ≃ R̂` as `k`-algebras with `tᵢ ↦ zᵢ`:
`k` maps onto the residue field, so the evaluation at the `zᵢ` is onto, and it is injective by
dimension. -/
private theorem exists_mvPowerSeries_algEquiv_adicCompletion {k R : Type*} [Field k]
    [IsAlgClosed k] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra k R]
    [Module.Finite k (ResidueField R)] {m : ℕ} {z : Fin m → R}
    (hz : MMP.Mori.IsRegularSystemOfParameters z) :
    ∃ G : MvPowerSeries (Fin m) k ≃ₐ[k] AdicCompletion (maximalIdeal R) R,
      ∀ i, G (MvPowerSeries.X i) = algebraMap R _ (z i) := by
  have hres : Function.Surjective (algebraMap k (ResidueField R)) :=
    (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := ResidueField R)).2
  have hsurj : Function.Surjective ((Ideal.Quotient.mk
      (maximalIdeal (AdicCompletion (maximalIdeal R) R))).comp
      (algebraMap k (AdicCompletion (maximalIdeal R) R))) := by
    intro w
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective w
    obtain ⟨r, hr⟩ := exists_algebraMap_sub_mem_pow (maximalIdeal R)
      (IsNoetherian.noetherian _) 1 x
    obtain ⟨c, hc⟩ := hres (residue R r)
    refine ⟨c, ?_⟩
    rw [RingHom.comp_apply, Ideal.Quotient.eq,
      IsScalarTower.algebraMap_apply k R (AdicCompletion (maximalIdeal R) R)]
    have h1 : algebraMap k R c - r ∈ maximalIdeal R := by
      rw [← residue_eq_zero_iff, map_sub, ← hc, IsScalarTower.algebraMap_apply k R (ResidueField R),
        ResidueField.algebraMap_eq, sub_self]
    have h2 : algebraMap R (AdicCompletion (maximalIdeal R) R) (algebraMap k R c) - x =
        algebraMap R _ (algebraMap k R c - r) - (x - algebraMap R _ r) := by
      rw [map_sub]
      ring
    rw [h2, AdicCompletion.maximalIdeal_eq_map]
    refine Ideal.sub_mem _ (Ideal.mem_map_of_mem _ h1) ?_
    simpa using hr
  obtain ⟨F, hFs, hFX, hFC⟩ := Stacks.CompleteLocalRing.CohenStructure.exists_surjective_eval₂Hom
    (maximalIdeal (AdicCompletion (maximalIdeal R) R))
    (fun i => algebraMap R (AdicCompletion (maximalIdeal R) R) (z i))
    (MMP.Flips.ResolutionInputs.span_range_algebraMap_eq_maximalIdeal hz)
    (algebraMap k (AdicCompletion (maximalIdeal R) R)) hsurj
  have hFi := MMP.Flips.ResolutionInputs.injective_of_surjective_of_ringKrullDim_le F hFs
    (MvPowerSeries.ringKrullDim_le k m)
    (by rw [← _root_.ringKrullDim_adicCompletion_maximalIdeal, hz.2])
  refine ⟨AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective F ⟨hFi, hFs⟩) fun c => ?_, hFX⟩
  change F (algebraMap k _ c) = _
  rw [← MMP.Flips.ResolutionInputs.mvPowerSeries_C_eq_algebraMap, hFC]

/-- Two distinct indices can be moved to the first two places by a permutation. -/
private theorem exists_perm_apply_zero_apply_one {n : ℕ} {a b : Fin (n + 1)} (hab : a ≠ b) :
    ∃ σ : Equiv.Perm (Fin (n + 1)), σ 0 = a ∧ σ 1 = b := by
  have h01 : (0 : Fin (n + 1)) ≠ 1 := by
    rcases n with _ | n
    · exact absurd (Fin.ext (by have := a.isLt; have := b.isLt; omega)) hab
    · simp
  have hb : Equiv.swap 0 a b ≠ 0 := by
    intro h
    have := congrArg (Equiv.swap 0 a) h
    rw [Equiv.swap_apply_self, Equiv.swap_apply_left] at this
    exact hab this.symm
  refine ⟨(Equiv.swap 1 (Equiv.swap 0 a b)).trans (Equiv.swap 0 a), ?_, ?_⟩
  · rw [Equiv.trans_apply, Equiv.swap_apply_of_ne_of_ne h01 hb.symm, Equiv.swap_apply_left]
  · rw [Equiv.trans_apply, Equiv.swap_apply_left, Equiv.swap_apply_self]

/-- Two distinct members `z_a`, `z_b` of a regular system of parameters satisfy
`(z_a) ∩ (z_b) = (z_a z_b)`. -/
public theorem span_inf_span_eq_span_mul {R : Type*} [CommRing R] [IsRegularLocalRing R] {N : ℕ}
    {z : Fin N → R} (hz : MMP.Mori.IsRegularSystemOfParameters z) {a b : Fin N} (hab : a ≠ b) :
    Ideal.span {z a} ⊓ Ideal.span {z b} = Ideal.span {z a * z b} := by
  have hp := MMP.Resolution.isPrime_span_singleton_of_isRegularSystemOfParameters hz b
  refine le_antisymm (fun v hv => ?_) (le_inf ?_ ?_)
  · obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hv.1
    have hc : c ∈ Ideal.span {z b} := (hp.mem_or_mem hv.2).resolve_right
      (MMP.Resolution.notMem_span_singleton_of_isRegularSystemOfParameters hz hab)
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hc
    exact Ideal.mem_span_singleton'.mpr ⟨d, by ring⟩
  · rw [Ideal.span_singleton_le_span_singleton]; exact dvd_mul_right _ _
  · rw [Ideal.span_singleton_le_span_singleton]; exact dvd_mul_left _ _

/-- **A transversal crossing of two branches is a double normal crossing.** Let `ι : T ⟶ X` be a
closed immersion, `X` locally of finite type over an algebraically closed field `k`, `x ∈ T` a
closed point and `z` a regular system of parameters of `𝒪_{X,ι(x)}` such that the kernel of
`𝒪_{X,ι(x)} → 𝒪_{T,x}` is `(z_a z_b)` for some `a ≠ b`. Then `𝒪̂_{T,x} ≅ k[[x₀, …, xₙ]]/(x₀x₁)`
as `k`-algebras. -/
public theorem hasCompletedLocalModel_of_ker_eq_span_mul {k : Type} [Field k] [IsAlgClosed k]
    {X T : Scheme.{0}} (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] (ι : T ⟶ X)
    [IsClosedImmersion ι] {x : T} (hx : IsClosed ({x} : Set T)) {n : ℕ}
    {z : Fin (n + 1) → X.presheaf.stalk (ι.base x)} (hz : MMP.Mori.IsRegularSystemOfParameters z)
    {a b : Fin (n + 1)} (hab : a ≠ b)
    (hker : RingHom.ker (ι.stalkMap x).hom = Ideal.span {z a * z b}) :
    HasCompletedLocalModel (ι ≫ sX) x
      (MvPowerSeries.X 0 * MvPowerSeries.X 1 : MvPowerSeries (Fin (n + 1)) k) := by
  have := LocallyOfFiniteType.isLocallyNoetherian sX
  have hy : IsClosed ({ι.base x} : Set X) := by
    have := ι.isClosedEmbedding.isClosedMap _ hx
    rwa [Set.image_singleton] at this
  let := MMP.Mori.stalkAlgebra sX (ι.base x)
  have : Module.Finite k (IsLocalRing.ResidueField (X.presheaf.stalk (ι.base x))) :=
    MMP.Flips.ResolutionInputs.finite_residueField_of_isClosed sX _ hy
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_apply_zero_apply_one hab
  have hz' : MMP.Mori.IsRegularSystemOfParameters (z ∘ σ) := by
    refine ⟨?_, hz.2⟩
    rw [Set.range_comp, σ.range_eq_univ, Set.image_univ]
    exact hz.1
  obtain ⟨G, hG⟩ := exists_mvPowerSeries_algEquiv_adicCompletion (k := k) hz'
  let : Algebra k (T.presheaf.stalk x) := (stalkStructureMap (ι ≫ sX) x).toAlgebra
  let φ : X.presheaf.stalk (ι.base x) →ₐ[k] T.presheaf.stalk x :=
    { (ι.stalkMap x).hom with
      commutes' := fun c => MMP.Flips.stalkMap_stalkStructureMap ι x c }
  exact nonempty_algEquiv_adicCompletion_of_surjective φ (ι.stalkMap_surjective x) G _ (z a * z b)
    (by rw [map_mul, hG 0, hG 1, ← map_mul]; simp only [Function.comp_apply, hσ0, hσ1]) hker

end Completion

/-- Being Cohen–Macaulay is invariant under linear equivalence. -/
public theorem isCMModule_of_linearEquiv {R M N : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (e : M ≃ₗ[R] N)
    (h : IsCMModule R M) : IsCMModule R N := by
  rcases h with h | ⟨xs, ⟨hm, hreg⟩, hlen⟩
  · exact Or.inl e.symm.toEquiv.subsingleton
  · exact Or.inr ⟨xs, ⟨hm, (e.isWeaklyRegular_congr xs).mp hreg⟩,
      by rw [hlen, Module.supportDim_eq_of_equiv e]⟩

section Depth

open RingTheory.Sequence IsLocalRing Abelian

universe v u

/-- **The depth lemma.** In a short exact sequence `0 → M₁ → M₂ → M₃ → 0` of finite modules over a
Noetherian local ring, if `M₁` and `M₂` have regular sequences of length `d` in the maximal ideal,
then `M₃ ≠ 0` has one of length `d - 1`. -/
private theorem exists_isRegular_of_shortExact {R : Type u} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Small.{v} R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    [Module.Finite R S.X₁] [Module.Finite R S.X₂] [Module.Finite R S.X₃] [Nontrivial S.X₃]
    {d : ℕ} {r₁ : List R} (h₁ : r₁.length = d) (m₁ : ∀ r ∈ r₁, r ∈ maximalIdeal R)
    (reg₁ : IsRegular S.X₁ r₁)
    {r₂ : List R} (h₂ : r₂.length = d) (m₂ : ∀ r ∈ r₂, r ∈ maximalIdeal R)
    (reg₂ : IsRegular S.X₂ r₂) :
    ∃ rs : List R, rs.length = d - 1 ∧ (∀ r ∈ rs, r ∈ maximalIdeal R) ∧ IsRegular S.X₃ rs := by
  let N := ModuleCat.of R (Shrink.{v} (R ⧸ maximalIdeal R))
  have hsupp : Module.support R N = PrimeSpectrum.zeroLocus (maximalIdeal R) := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus,
      Ideal.annihilator_quotient]
  have hlt : ∀ (M : ModuleCat.{v} R) [Module.Finite R M] [Nontrivial M],
      maximalIdeal R • (⊤ : Submodule R M) < ⊤ := fun M _ _ =>
    (Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator
      (IsLocalRing.maximalIdeal_le_jacobson _)).symm.lt_top
  have nt₁ : Nontrivial S.X₁ := reg₁.nontrivial
  have nt₂ : Nontrivial S.X₂ := reg₂.nontrivial
  have e₁ := ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) N hsupp.le S.X₁
    (hlt _) r₁ m₁ reg₁
  have e₂ := ModuleCat.subsingleton_ext_of_exists_isRegular (maximalIdeal R) N hsupp.le S.X₂
    (hlt _) r₂ m₂ reg₂
  have e₃ : ∀ i < d - 1, Subsingleton (Ext N S.X₃ i) := by
    intro i hi
    have zero1 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (e₂ i (by omega))
    have zero2 := AddCommGrpCat.isZero_of_iff_subsingleton.mpr (e₁ (i + 1) (by omega))
    exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
      ((Ext.covariant_sequence_exact₃' N hS) i (i + 1) rfl)
      (zero1.eq_zero_of_src _) (zero2.eq_zero_of_tgt _)
  have : Module.Finite R N := Module.Finite.equiv (Shrink.linearEquiv R _).symm
  exact ModuleCat.exists_isRegular_of_exists_subsingleton_ext
    (maximalIdeal R) (d - 1) S.X₃ (hlt _) N hsupp e₃

/-- An element of `WithBot ℕ∞` with a finite successor is a natural number. -/
private theorem exists_natCast_eq_of_add_one_eq {x : WithBot ℕ∞} {d : ℕ}
    (h : x + ((1 : ℕ) : WithBot ℕ∞) = ((d : ℕ∞) : WithBot ℕ∞)) :
    ∃ a : ℕ, x = ((a : ℕ∞) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd h (by simp)
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => exfalso; norm_cast at h
    | coe e => exact ⟨e, rfl⟩

/-- **A Cohen–Macaulay ideal cuts out a Cohen–Macaulay quotient.** Let `R` be a Noetherian local
domain which is Cohen–Macaulay, and `φ : R → A` a surjection onto a local ring whose kernel is a
nonzero ideal which is a Cohen–Macaulay `R`-module. Then `A` is a Cohen–Macaulay ring, of dimension
`dim R - 1`. -/
public theorem isCMModule_of_surjective_of_isCMModule_ker {R A : Type u} [CommRing R]
    [IsLocalRing R] [IsNoetherianRing R] [IsDomain R] [CommRing A] [IsLocalRing A]
    (φ : R →+* A) (hφ : Function.Surjective φ) (hI0 : RingHom.ker φ ≠ ⊥)
    (hR : IsCMModule R R) (hI : IsCMModule R (RingHom.ker φ)) : IsCMModule A A := by
  let := φ.toAlgebra
  set I := RingHom.ker φ with hIdef
  have hI1 : I ≠ ⊤ := RingHom.ker_ne_top φ
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI0
  have : IsLocalHom φ := IsLocalHom.of_surjective _ hφ
  have : IsNoetherianRing A := isNoetherianRing_of_surjective R A φ hφ
  have hmem : ∀ r ∈ maximalIdeal R, φ r ∈ maximalIdeal A := fun r hr =>
    (IsLocalRing.mem_maximalIdeal _).mpr fun h =>
      (IsLocalRing.mem_maximalIdeal _).mp hr (isUnit_of_map_unit φ r h)
  obtain hR | ⟨xs, ⟨hxm, hxs⟩, hxl⟩ := hR
  · exact absurd hR (not_subsingleton R)
  obtain hI | ⟨ys, ⟨hym, hys⟩, hyl⟩ := hI
  · exact absurd hI (not_subsingleton I)
  rw [Module.supportDim_self_eq_ringKrullDim] at hxl
  have hann : Module.annihilator R I = ⊥ := by
    obtain ⟨⟨f, hfI⟩, hf0⟩ := exists_ne (0 : I)
    refine eq_bot_iff.mpr fun r hr => ?_
    have h := Module.mem_annihilator.mp hr ⟨f, hfI⟩
    have hf : f ≠ 0 := fun h' => hf0 (Subtype.ext h')
    have : r * f = 0 := congrArg Subtype.val h
    exact (mul_eq_zero.mp this).resolve_right hf
  rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, hann,
    ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)] at hyl
  have hlen : ys.length = xs.length := by exact_mod_cast hyl.trans hxl.symm
  -- the short exact sequence `0 → I → R → A → 0`
  let S := (Algebra.linearMap R A).shortComplexKer
  have hS : S.ShortExact := LinearMap.shortExact_shortComplexKer hφ
  let e : LinearMap.ker (Algebra.linearMap R A) ≃ₗ[R] I := LinearEquiv.ofEq _ _ rfl
  have : Nontrivial (LinearMap.ker (Algebra.linearMap R A)) := e.toEquiv.nontrivial
  have : Module.Finite R S.X₁ := Module.Finite.equiv e.symm
  have : Module.Finite R S.X₂ := inferInstanceAs (Module.Finite R R)
  have : Module.Finite R A := Module.Finite.of_surjective (Algebra.linearMap R A) hφ
  have : Module.Finite R S.X₃ := inferInstanceAs (Module.Finite R A)
  have : Nontrivial S.X₃ := inferInstanceAs (Nontrivial A)
  have reg₁ : IsRegular S.X₁ ys :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal
      (M := LinearMap.ker (Algebra.linearMap R A)) hym).mpr ((e.isWeaklyRegular_congr ys).mpr hys)
  have reg₂ : IsRegular S.X₂ xs :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (M := R) hxm).mpr hxs
  obtain ⟨rs, hrl, hrm, hreg⟩ := exists_isRegular_of_shortExact S hS hlen hym reg₁ rfl hxm reg₂
  change IsRegular A rs at hreg
  -- the regular sequence on `A`
  have hrm' : ∀ r ∈ rs.map (algebraMap R A), r ∈ maximalIdeal A := fun r hr => by
    obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hr
    exact hmem r (hrm r hr')
  have hreg' : IsRegular A (rs.map (algebraMap R A)) :=
    (IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal hrm').mpr
      ((isWeaklyRegular_map_algebraMap_iff A A rs).mpr hreg.1)
  refine Or.inr ⟨_, ⟨hrm', hreg'.1⟩, ?_⟩
  rw [Module.supportDim_self_eq_ringKrullDim]
  -- the dimension count `dim A = dim R - 1`
  obtain ⟨f, hfI, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI0
  have hfm : f ∈ maximalIdeal R := IsLocalRing.le_maximalIdeal hI1 hfI
  have hfreg : IsRegular R [f] := by
    rw [IsLocalRing.isRegular_iff_isWeaklyRegular_of_subset_maximalIdeal (by simpa using hfm)]
    simpa using IsSMulRegular.of_ne_zero hf0
  have h1 := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular [f] hfreg
  have hle : ringKrullDim A ≤ ringKrullDim (R ⧸ Ideal.ofList [f]) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.lift (Ideal.ofList [f]) φ (by
      intro a ha
      have : Ideal.ofList [f] ≤ I := by
        simpa [Ideal.ofList] using (Ideal.span_singleton_le_iff_mem I).mpr hfI
      exact this ha))
      (Ideal.Quotient.lift_surjective_of_surjective _ _ hφ)
  have h2 := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular _ hreg'
  have hnt : Nontrivial (A ⧸ Ideal.ofList (rs.map (algebraMap R A))) :=
    Ideal.Quotient.nontrivial_iff.mpr fun h => hreg'.2 (by rw [h, Submodule.top_smul])
  have h0 : 0 ≤ ringKrullDim (A ⧸ Ideal.ofList (rs.map (algebraMap R A))) :=
    ringKrullDim_nonneg_of_nontrivial
  rw [List.length_singleton, ← hxl] at h1
  obtain ⟨a, ha⟩ := exists_natCast_eq_of_add_one_eq h1
  rw [ha] at h1 hle
  have had : a + 1 = xs.length := by exact_mod_cast h1
  refine le_antisymm ?_ ?_
  · rw [← h2]; exact le_add_of_nonneg_left h0
  · refine hle.trans ?_
    rw [List.length_map, hrl]; exact_mod_cast (by omega : a ≤ xs.length - 1)

end Depth

end MMP.Fourfold.SdltFloor
