module

public import StacksFrontier.AlgebraicGeometry.ProjQuotientFiniteCover.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseIso
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjAndSpecBaseChange
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Comparison
public import StacksFrontier.AlgebraicGeometry.ProjPolyChart.Cover
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-!
# Noether normalization for projective schemes

Let `X` be a closed subscheme of projective space `ℙᴺ_K = Proj K[x₀, …, x_N]` over a field `K`,
of dimension `n`. Then there is a finite surjective morphism `X ⟶ ℙⁿ_K` over `K`. In particular
this holds for every projective variety of dimension `n`.

The proof is the classical one through the homogeneous coordinate ring. Write
`X = Proj B` with `B = K[x₀, …, x_N] / I` graded by degree. Cutting `Proj B` successively by
homogeneous elements `η₀, η₁, …` of positive degree, each chosen (by graded prime avoidance)
outside the generic points of the finitely many irreducible closed pieces of what remains, every
point that survives `k` cuts is the bottom of a strict chain of generizations of length `k`;
since `dim X = n`, nothing survives `n + 1` cuts. Raising the `ηⱼ` to suitable powers puts them
in one degree `D`, and then `x ↦ (η₀(x) : ⋯ : ηₙ(x))` is a morphism `X ⟶ ℙⁿ` over `K`: it is
the identification `Proj B ≅ Proj B⁽ᴰ⁾` with the Veronese subring followed by the morphism
induced by `K[y₀, …, yₙ] → B⁽ᴰ⁾`, `yⱼ ↦ ηⱼ`. The preimage of the chart `{yⱼ ≠ 0}` is the affine
open `D₊(ηⱼ)`, so the morphism is affine; it is proper because `X` is proper over `K`; hence it
is finite. A finite morphism carries strict chains of points to strict chains, so its closed
image has dimension `n = dim ℙⁿ` and is all of the irreducible space `ℙⁿ`.

## Main results

* `MMP.ProjectiveSpace.exists_isFinite_surjective`: a closed subscheme of `ℙᴺ_K` of dimension `n`
  admits a finite surjective morphism to `ℙⁿ_K` over `K`.
* `MMP.ProjectiveSpace.NoetherNormalization.exists_homogeneous_notMem`: graded prime avoidance,
  over an arbitrary graded ring and with no hypothesis on the base field.
* `MMP.ProjectiveSpace.NoetherNormalization.exists_homogeneous_family`: if `Proj 𝒜` is a
  Noetherian space of dimension at most `n`, there are `n + 1` homogeneous elements of one positive
  degree without common zero on `Proj 𝒜`.
* `MMP.ProjectiveSpace.NoetherNormalization.surjective_of_isFinite`: a finite morphism between
  schemes of the same finite dimension with irreducible target is surjective.
* `MMP.ProjectiveSpace.NoetherNormalization.projToProjectiveSpace`: the morphism `Proj B ⟶ ℙⁿ`
  defined by such homogeneous elements, with `isAffineHom_projToProjectiveSpace` and its
  compatibility `projToProjectiveSpace_comp_projToSpecCoeff` with the structure morphisms.

## Implementation notes

Projective space `ℙⁿ_K` is `Proj (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading K n)`, lying
over `Spec K` through `Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff K n`. The statement
names the structure morphisms explicitly: `X` is a closed subscheme of `ℙᴺ_K` through a closed
immersion `ι`, a `K`-scheme through `ι ≫ projToSpecCoeff K N`, and the finite morphism `f`
commutes with these. Neither integrality nor reducedness of `X` is used. The dimension is the
Krull dimension of the underlying space.

The parameters are taken in a common degree `D`, not in degree one: over a finite field a
projective variety need not admit a linear projection that is finite (all `K`-rational points
of `ℙᴺ` may lie on it), and the degree-`D` parameters are what makes the argument field-free.

## References

* [W. Fulton, *Intersection Theory*][fulton1998], §18.3, Step 8.
* [D. Mumford, *The Red Book of Varieties and Schemes*], Chapter I, §7.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

namespace MMP.ProjectiveSpace

namespace NoetherNormalization

/-! ### Graded prime avoidance -/

section Avoidance

variable {A : Type*} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- If a homogeneous ideal `p` is not contained in a homogeneous ideal `q`, some homogeneous
element of `p` lies outside `q`. -/
theorem exists_homogeneous_mem_notMem {p q : HomogeneousIdeal 𝒜}
    (h : ¬ p.toIdeal ≤ q.toIdeal) : ∃ m : ℕ, ∃ a ∈ 𝒜 m, a ∈ p.toIdeal ∧ a ∉ q.toIdeal := by
  classical
  by_contra! H
  refine h fun x hx => ?_
  rw [← DirectSum.sum_support_decompose 𝒜 x]
  exact Ideal.sum_mem _ fun i _ =>
    H i _ (SetLike.coe_mem _) (p.isHomogeneous i hx)

/-- A relevant homogeneous prime misses some homogeneous element of positive degree. -/
theorem exists_pos_homogeneous_notMem (q : ProjectiveSpectrum 𝒜) :
    ∃ m : ℕ, 0 < m ∧ ∃ a ∈ 𝒜 m, a ∉ q.asHomogeneousIdeal.toIdeal := by
  obtain ⟨n, f, hn, hf, h⟩ :=
    Stacks.AlgebraicGeometry.ProjShared.exists_homogeneous_pos_notMem 𝒜 q
  exact ⟨n, hn, f, hf, h⟩

/-- If `x` lies in a prime ideal and `y` does not, then neither does `x ^ b + y ^ a` for
`b > 0`. -/
theorem pow_add_pow_notMem_of_mem_of_notMem {R : Type*} [CommRing R] {I : Ideal R}
    (hI : I.IsPrime) {x y : R} {a b : ℕ} (hb : 0 < b) (hx : x ∈ I) (hy : y ∉ I) :
    x ^ b + y ^ a ∉ I := fun hsum =>
  hy (hI.mem_of_pow_mem _ (by simpa using I.sub_mem hsum (I.pow_mem_of_mem hx _ hb)))

/-- **Graded prime avoidance for an antichain.** Finitely many pairwise incomparable relevant
homogeneous primes all miss a single homogeneous element of positive degree. -/
theorem exists_homogeneous_notMem_of_antichain (P : Finset (ProjectiveSpectrum 𝒜))
    (hP : ∀ p ∈ P, ∀ q ∈ P, p.asHomogeneousIdeal.toIdeal ≤ q.asHomogeneousIdeal.toIdeal →
      p = q) :
    ∃ d : ℕ, 0 < d ∧ ∃ a ∈ 𝒜 d, ∀ p ∈ P, a ∉ p.asHomogeneousIdeal.toIdeal := by
  classical
  induction P using Finset.induction_on with
  | empty => exact ⟨1, one_pos, 0, zero_mem _, by simp⟩
  | insert q P hqP ih =>
    obtain ⟨a, ha, f, hf, hfP⟩ := ih fun p hp p' hp' h =>
      hP p (Finset.mem_insert_of_mem hp) p' (Finset.mem_insert_of_mem hp') h
    by_cases hfq : f ∈ q.asHomogeneousIdeal.toIdeal
    swap
    · refine ⟨a, ha, f, hf, fun p hp => ?_⟩
      rcases Finset.mem_insert.mp hp with rfl | hp
      · exact hfq
      · exact hfP p hp
    have hne : ∀ p ∈ P, ¬ p.asHomogeneousIdeal.toIdeal ≤ q.asHomogeneousIdeal.toIdeal :=
      fun p hp hle => hqP (hP p (Finset.mem_insert_of_mem hp) q (Finset.mem_insert_self _ _)
        hle ▸ hp)
    choose! m h hhm hhp hhq using fun p hp => exists_homogeneous_mem_notMem 𝒜 (hne p hp)
    obtain ⟨c, hc, g, hg, hgq⟩ := exists_pos_homogeneous_notMem 𝒜 q
    set H : A := g * ∏ p ∈ P, h p with hH_def
    set b : ℕ := c + ∑ p ∈ P, m p with hb_def
    have hb : 0 < b := by omega
    have hH : H ∈ 𝒜 b := SetLike.mul_mem_graded hg (SetLike.prod_mem_graded 𝒜 m h
      fun p hp => hhm p hp)
    have hHq : H ∉ q.asHomogeneousIdeal.toIdeal := by
      rw [hH_def]
      refine q.isPrime.mul_notMem hgq fun hmem => ?_
      obtain ⟨p, hp, hpq⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact hhq p hp hpq
    have hHp : ∀ p ∈ P, H ∈ p.asHomogeneousIdeal.toIdeal := fun p hp =>
      Ideal.mul_mem_left _ _ (by
        rw [← Finset.prod_erase_mul _ _ hp]
        exact Ideal.mul_mem_left _ _ (hhp p hp))
    refine ⟨a * b, Nat.mul_pos ha hb, f ^ b + H ^ a, ?_, fun p hp => ?_⟩
    · refine add_mem ?_ ?_
      · simpa [smul_eq_mul, mul_comm] using SetLike.pow_mem_graded b hf
      · simpa [smul_eq_mul] using SetLike.pow_mem_graded a hH
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact pow_add_pow_notMem_of_mem_of_notMem p.isPrime hb hfq hHq
    · rw [add_comm]
      exact pow_add_pow_notMem_of_mem_of_notMem p.isPrime ha (hHp p hp) (hfP p hp)

/-- **Graded prime avoidance.** Finitely many relevant homogeneous primes all miss a single
homogeneous element of positive degree. -/
theorem exists_homogeneous_notMem (P : Set (ProjectiveSpectrum 𝒜)) (hP : P.Finite) :
    ∃ d : ℕ, 0 < d ∧ ∃ a ∈ 𝒜 d, ∀ p ∈ P, a ∉ p.asHomogeneousIdeal.toIdeal := by
  classical
  let M : Set (ProjectiveSpectrum 𝒜) := {q | Maximal (· ∈ P) q}
  have hM : M.Finite := hP.subset fun q hq => hq.prop
  obtain ⟨d, hd, a, ha, haM⟩ := exists_homogeneous_notMem_of_antichain 𝒜 hM.toFinset
    fun p hp q hq hle => by
      rw [Set.Finite.mem_toFinset] at hp hq
      exact le_antisymm hle (hp.2 hq.1 hle)
  refine ⟨d, hd, a, ha, fun p hp hap => ?_⟩
  obtain ⟨q, hpq, hq⟩ := hP.exists_le_maximal hp
  exact haM q (hM.mem_toFinset.mpr hq) (hpq hap)

end Avoidance

/-! ### Dimension of a scheme through chains of points -/

section Chains

/-- The dimension of a scheme is the Krull dimension of its set of points ordered by
specialization (`x ≤ y` when `y ⤳ x`). -/
theorem topologicalKrullDim_eq_krullDim (X : Scheme.{u}) :
    topologicalKrullDim X = Order.krullDim X :=
  Order.krullDim_eq_of_orderIso irreducibleSetEquivPoints

/-- In a scheme, a proper specialization is a strict inequality for the specialization order. -/
theorem lt_of_specializes_of_ne {X : Scheme.{u}} {x y : X} (h : y ⤳ x) (hne : x ≠ y) : x < y :=
  lt_iff_le_not_ge.mpr ⟨Scheme.le_iff_specializes.mpr h,
    fun h' => hne ((Scheme.le_iff_specializes.mp h').antisymm h).eq⟩

/-- A locally quasi-finite morphism (for instance a finite one) maps a strict specialization to a
strict specialization: its fibres are discrete. -/
theorem lt_map_of_lt {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] {x x' : X}
    (h : x < x') : f x < f x' := by
  have hle : x' ⤳ x := Scheme.le_iff_specializes.mp h.le
  refine lt_of_specializes_of_ne (hle.map f.continuous) fun heq => ?_
  have hdisc : DiscreteTopology (f ⁻¹' {f x}) :=
    (f.isDiscrete_preimage_singleton (f x)).to_subtype
  have hsp : (⟨x', heq.symm⟩ : f ⁻¹' {f x}) ⤳ ⟨x, rfl⟩ := subtype_specializes_iff _ _ |>.mpr hle
  exact h.ne' (congrArg Subtype.val (specializes_iff_eq.mp hsp))

/-- **A finite morphism between schemes of the same finite dimension, with irreducible target,
is surjective.** A maximal chain of points of `X` maps to a chain of the same length in `Y`; if
`f` missed a point, its closed image would miss the generic point of `Y`, which would extend the
chain beyond the dimension of `Y`. -/
theorem surjective_of_isFinite {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IrreducibleSpace Y]
    {n : ℕ} (hX : topologicalKrullDim X = n) (hY : topologicalKrullDim Y = n) :
    Surjective f := by
  rw [topologicalKrullDim_eq_krullDim] at hX hY
  obtain ⟨s, hs⟩ := Order.le_krullDim_iff.mp hX.ge
  let t : LTSeries Y :=
    { length := s.length
      toFun := fun i => f (s i)
      step := fun i => lt_map_of_lt f (s.step i) }
  constructor
  by_contra hns
  have hξ : genericPoint Y ∉ Set.range f := by
    refine fun hmem => hns ?_
    have hsub : closure {genericPoint Y} ⊆ Set.range f :=
      f.isClosedMap.isClosed_range.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)
    rw [(genericPoint_spec Y).def] at hsub
    exact fun y => hsub (Set.mem_univ y)
  have hlast : t.last < genericPoint Y :=
    lt_of_specializes_of_ne ((genericPoint_spec Y).specializes (Set.mem_univ _))
      fun h => hξ ⟨s.last, h⟩
  have h1 := Order.LTSeries.length_le_krullDim (t.snoc (genericPoint Y) hlast)
  rw [hY] at h1
  simp only [RelSeries.snoc_length, t, hs] at h1
  norm_cast at h1
  omega

end Chains

/-! ### Cutting down `Proj` by homogeneous elements -/

section Cutting

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- After cutting `Proj 𝒜` by `k` well-chosen homogeneous elements of positive degree, every
point that remains is the bottom of a strict chain of generizations of length `k`. Each new
element is chosen, by graded prime avoidance, outside the generic points of the finitely many
irreducible closed pieces of what remains. -/
theorem exists_family_ltSeries [TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Proj 𝒜)]
    (k : ℕ) :
    ∃ (d : Fin k → ℕ) (η : Fin k → A), (∀ j, 0 < d j ∧ η j ∈ 𝒜 (d j)) ∧
      ∀ y : AlgebraicGeometry.Proj 𝒜, (∀ j, η j ∈ y.asHomogeneousIdeal.toIdeal) →
        ∃ s : LTSeries (AlgebraicGeometry.Proj 𝒜), s.length = k ∧ s.head = y := by
  induction k with
  | zero =>
    exact ⟨fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun y _ => ⟨RelSeries.singleton _ y, rfl, rfl⟩⟩
  | succ k ih =>
    obtain ⟨d, η, hdη, hs⟩ := ih
    let Y : Set (AlgebraicGeometry.Proj 𝒜) :=
      ⋂ j, ((Proj.basicOpen 𝒜 (η j) : Set (AlgebraicGeometry.Proj 𝒜)))ᶜ
    have hYc : IsClosed Y :=
      isClosed_iInter fun j => (Proj.basicOpen 𝒜 (η j)).isOpen.isClosed_compl
    have hmemY : ∀ y : AlgebraicGeometry.Proj 𝒜,
        y ∈ Y ↔ ∀ j, η j ∈ y.asHomogeneousIdeal.toIdeal := by
      intro y
      simp [Y, Proj.mem_basicOpen]
    obtain ⟨S, hSfin, hSc, hSirr, hYS⟩ :=
      TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hYc
    let G : Set (AlgebraicGeometry.Proj 𝒜) := ⋃ t ∈ S, {g | IsGenericPoint g t}
    have hG : G.Finite :=
      hSfin.biUnion fun t _ => Set.Subsingleton.finite fun g hg g' hg' => hg.eq hg'
    obtain ⟨d', hd', η', hη', hη'G⟩ := exists_homogeneous_notMem 𝒜 G hG
    refine ⟨Fin.snoc d d', Fin.snoc η η', fun j => ?_, fun y hy => ?_⟩
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa using ⟨hd', hη'⟩
      · simpa using hdη j
    · have hyη : ∀ j, η j ∈ y.asHomogeneousIdeal.toIdeal := fun j => by
        simpa using hy j.castSucc
      have hyη' : η' ∈ y.asHomogeneousIdeal.toIdeal := by simpa using hy (Fin.last k)
      have hyY : y ∈ Y := (hmemY y).mpr hyη
      rw [hYS] at hyY
      obtain ⟨t, htS, hyt⟩ := Set.mem_sUnion.mp hyY
      obtain ⟨g, hg⟩ := QuasiSober.sober (hSirr t htS) (hSc t htS)
      have hgG : g ∈ G := Set.mem_biUnion htS hg
      have hgY : g ∈ Y := hYS ▸ Set.mem_sUnion_of_mem hg.mem htS
      obtain ⟨s, hslen, hshead⟩ := hs g ((hmemY g).mp hgY)
      have hlt : y < s.head := hshead ▸ lt_of_specializes_of_ne (hg.specializes hyt)
        fun h => hη'G g hgG (h ▸ hyη')
      exact ⟨s.cons y hlt, by simp [hslen], by simp⟩

/-- **Homogeneous parameters.** If `Proj 𝒜` is a Noetherian space of dimension at most `n`, there
are `n + 1` homogeneous elements of one positive degree with no common zero on `Proj 𝒜`. -/
theorem exists_homogeneous_family [TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Proj 𝒜)]
    {n : ℕ}
    (hdim : topologicalKrullDim (AlgebraicGeometry.Proj 𝒜) ≤ n) :
    ∃ D : ℕ, 0 < D ∧ ∃ η : Fin (n + 1) → A, (∀ j, η j ∈ 𝒜 D) ∧
      ∀ y : AlgebraicGeometry.Proj 𝒜, ∃ j, η j ∉ y.asHomogeneousIdeal.toIdeal := by
  classical
  obtain ⟨d, η, hdη, hs⟩ := exists_family_ltSeries 𝒜 (n + 1)
  refine ⟨∏ j, d j, Finset.prod_pos fun j _ => (hdη j).1,
    fun j => η j ^ ∏ i ∈ Finset.univ.erase j, d i, fun j => ?_, fun y => ?_⟩
  · have := SetLike.pow_mem_graded (∏ i ∈ Finset.univ.erase j, d i) (hdη j).2
    rwa [smul_eq_mul, Finset.prod_erase_mul _ _ (Finset.mem_univ j)] at this
  · by_contra! h
    obtain ⟨s, hslen, -⟩ := hs y fun j => y.isPrime.mem_of_pow_mem _ (h j)
    have h1 := Order.LTSeries.length_le_krullDim s
    rw [← topologicalKrullDim_eq_krullDim, hslen] at h1
    have h2 := h1.trans hdim
    norm_cast at h2
    omega

end Cutting

/-! ### The Veronese subring and the structure morphism -/

section Veronese

open Stacks.Veronese

variable {S : Type u} {σ : Type*} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮] (d : ℕ)

/-- The degree-zero part of the `d`-th Veronese subring is the degree-zero part of the ring. -/
def veroneseZeroHom : veroneseGrading 𝒮 d 0 →+* 𝒮 0 where
  toFun x := ⟨((x : veroneseSubring 𝒮 d) : S), by
    simpa using (mem_veroneseGrading 𝒮).mp x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The degree-zero comparison is the inclusion of the Veronese subring. -/
theorem coe_veroneseZeroHom (x : veroneseGrading 𝒮 d 0) :
    (veroneseZeroHom 𝒮 d x : S) = ((x : veroneseSubring 𝒮 d) : S) := rfl

/-- A degree-zero element, viewed in a homogeneous localization, is the fraction `a / 1`. -/
theorem val_fromZeroRingHom (x : Submonoid S) (a : 𝒮 0) :
    (HomogeneousLocalization.fromZeroRingHom 𝒮 x a).val = Localization.mk (a : S) 1 :=
  rfl

/-- The isomorphism `Proj S ≅ Proj S⁽ᵈ⁾` commutes with the structure morphisms to the spectra of
the degree-zero parts. -/
theorem veroneseProjIso_hom_toSpecZero (hd : 0 < d) :
    letI := veroneseGradingGradedRing 𝒮 d hd
    (veroneseProjIso 𝒮 d hd).hom ≫ Proj.toSpecZero (veroneseGrading 𝒮 d) =
      Proj.toSpecZero 𝒮 ≫ Spec.map (CommRingCat.ofHom (veroneseZeroHom 𝒮 d)) := by
  let := veroneseGradingGradedRing 𝒮 d hd
  have key : ∀ (f : S) {e : ℕ} (he : 0 < e) (hf : f ∈ 𝒮 e),
      Proj.awayι 𝒮 f hf he ≫ (veroneseProjIso 𝒮 d hd).hom ≫
        Proj.toSpecZero (veroneseGrading 𝒮 d) =
      Proj.awayι 𝒮 f hf he ≫ Proj.toSpecZero 𝒮 ≫
        Spec.map (CommRingCat.ofHom (veroneseZeroHom 𝒮 d)) := by
    intro f e he hf
    have h1 : veroneseChart 𝒮 d hd f he hf ≫ (veroneseProjIso 𝒮 d hd).inv =
        Proj.awayι 𝒮 f hf he :=
      veroneseChart_comp_veroneseProjInv 𝒮 d hd f he hf
    have hchart : Proj.awayι 𝒮 f hf he ≫ (veroneseProjIso 𝒮 d hd).hom =
        veroneseChart 𝒮 d hd f he hf := by
      rw [← h1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% hchart]
    dsimp only [veroneseChart]
    rw [Category.assoc, Proj.awayι_toSpecZero, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp,
      ← Spec.map_comp]
    congr 1
    ext x
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp, Function.comp_apply,
      RingEquiv.toCommRingCatIso_hom, RingHom.coe_coe,
      val_veroneseAwayEquiv, val_fromZeroRingHom, veroneseLocalizationMap_mk]
    rfl
  exact (Proj.affineOpenCover 𝒮).openCover.hom_ext _ _ fun i => key i.2.1 i.1.2 i.2.2

end Veronese

/-! ### The structure morphism of projective space -/

section StructureMorphism

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The structure morphism `ℙⁿ_K ⟶ Spec K` is `Proj 𝒜 ⟶ Spec 𝒜₀` followed by `K → 𝒜₀`. -/
theorem projToSpecCoeff_eq (K : Type u) [Field K] (n : ℕ) :
    projToSpecCoeff K n = Proj.toSpecZero (polyGrading K n) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (polyGrading K n 0))) := by
  rw [projToSpecCoeff]
  congr 2
  refine CommRingCat.hom_ext (RingHom.ext fun c => Subtype.ext ?_)
  change ((DirectSum.decompose (polyGrading K n) (algebraMap K _ c)) 0 :
    MvPolynomial (Fin (n + 1)) K) = algebraMap K _ c
  exact DirectSum.decompose_of_mem_same _ (SetLike.algebraMap_mem_graded _ c)

end StructureMorphism

/-! ### The morphism to projective space defined by homogeneous parameters -/

section Projection

open Stacks.Veronese Stacks.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {B : Type u} [CommRing B] [Algebra K B]
  (ℬ : ℕ → Submodule K B) [GradedAlgebra ℬ] {D : ℕ} (hD : 0 < D) {n : ℕ}
  (η : Fin (n + 1) → B) (hη : ∀ j, η j ∈ ℬ D)

/-- The scalars `K → B`, as elements of the `D`-th Veronese subring. -/
def veroneseConst : K →+* veroneseSubring ℬ D :=
  (algebraMap K B).codRestrict (veroneseSubring ℬ D) fun c =>
    mem_veroneseSubring_of_mem ℬ (n := 0) (by simpa using SetLike.algebraMap_mem_graded ℬ c)

/-- An element `ηⱼ` of degree `D`, as an element of the `D`-th Veronese subring. -/
def veroneseElem (j : Fin (n + 1)) : veroneseSubring ℬ D :=
  ⟨η j, mem_veroneseSubring_of_mem ℬ (n := 1) (by simpa using hη j)⟩

/-- The graded homomorphism `K[y₀, …, yₙ] → B⁽ᴰ⁾`, `yⱼ ↦ ηⱼ`, into the `D`-th Veronese subring,
where `ηⱼ` has degree one. -/
def evalHom : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K →+*ᵍ veroneseGrading ℬ D where
  toRingHom := MvPolynomial.eval₂Hom (veroneseConst ℬ) (veroneseElem ℬ η hη)
  map_mem {i x} hx := by
    rw [MvPolynomial.mem_homogeneousSubmodule] at hx
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq']
    refine sum_mem fun α hα => ?_
    have hdeg : ∑ j, α j = i := by
      simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using
        hx (MvPolynomial.mem_support_iff.mp hα)
    have h0 : veroneseConst ℬ (x.coeff α) ∈ veroneseGrading ℬ D 0 :=
      (mem_veroneseGrading ℬ).mpr (by
        simpa [veroneseConst] using SetLike.algebraMap_mem_graded ℬ (x.coeff α))
    have h1 := SetLike.prod_pow_mem_graded (veroneseGrading ℬ D) (fun _ => 1)
      (veroneseElem ℬ η hη) (F := Finset.univ) α
      (fun j _ => (mem_veroneseGrading ℬ).mpr (by simpa [veroneseElem] using hη j))
    simpa [hdeg] using SetLike.mul_mem_graded h0 h1

/-- `yⱼ ↦ ηⱼ`. -/
theorem evalHom_X (j : Fin (n + 1)) :
    evalHom ℬ η hη (MvPolynomial.X j) = veroneseElem ℬ η hη j := by
  simp [evalHom]

/-- Scalars go to scalars. -/
theorem evalHom_C (c : K) :
    evalHom ℬ η hη (MvPolynomial.C c) = veroneseConst ℬ c := by
  simp [evalHom]

variable (hcov : ∀ y : AlgebraicGeometry.Proj ℬ, ∃ j, η j ∉ y.asHomogeneousIdeal.toIdeal)

include hcov in
/-- If the `ηⱼ` have no common zero on `Proj B`, the induced map of projective spectra is
everywhere defined. -/
theorem mapDomain_evalHom_eq_top :
    letI := veroneseGradingGradedRing ℬ D hD
    ProjShared.mapDomain _ _ (evalHom ℬ η hη) = ⊤ := by
  let := veroneseGradingGradedRing ℬ D hD
  refine top_le_iff.mp fun y _ => (ProjShared.mem_mapDomain_iff _ _ _ y).mpr ?_
  obtain ⟨j, hj⟩ := hcov ((veroneseProjIso ℬ D hD).inv y)
  refine ⟨1, MvPolynomial.X j, one_pos,
    (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X K j),
    fun hmem => hj ?_⟩
  have hy : (veroneseProjIso ℬ D hD).hom ((veroneseProjIso ℬ D hD).inv y) = y := by
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    rfl
  rw [← hy] at hmem
  simpa [evalHom_X, veroneseElem] using
    (veroneseProjIso_mem_iff ℬ D hD _ (evalHom ℬ η hη (MvPolynomial.X j))).mp hmem

/-- The morphism `Proj B ⟶ ℙⁿ`, `x ↦ (η₀(x) : ⋯ : ηₙ(x))`, defined by homogeneous elements of
one positive degree with no common zero: the identification `Proj B ≅ Proj B⁽ᴰ⁾` followed by the
morphism induced by `K[y₀, …, yₙ] → B⁽ᴰ⁾`, `yⱼ ↦ ηⱼ`. -/
def projToProjectiveSpace : AlgebraicGeometry.Proj ℬ ⟶ AlgebraicGeometry.Proj (polyGrading K n) :=
  letI := veroneseGradingGradedRing ℬ D hD
  (veroneseProjIso ℬ D hD).hom ≫
    RelativeProj.mapHomOfTop _ _ (evalHom ℬ η hη) (mapDomain_evalHom_eq_top ℬ hD η hη hcov)

/-- The morphism defined by homogeneous parameters is affine: the preimage of the standard chart
`{yⱼ ≠ 0}` is the affine open `D₊(ηⱼ)`. -/
theorem isAffineHom_projToProjectiveSpace :
    IsAffineHom (projToProjectiveSpace ℬ hD η hη hcov) := by
  let := veroneseGradingGradedRing ℬ D hD
  have : IsAffineHom (RelativeProj.mapHomOfTop _ _ (evalHom ℬ η hη)
      (mapDomain_evalHom_eq_top ℬ hD η hη hcov)) := by
    refine isAffineHom_of_forall_exists_isAffineOpen _ fun z => ?_
    obtain ⟨i, hi⟩ := Stacks.ProjectiveSpace.exists_mem_basicOpen_X z
    have hX : (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) K) ∈
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K 1 :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X K i)
    refine ⟨_, hi, Proj.isAffineOpen_basicOpen _ _ hX one_pos, ?_⟩
    rw [ProjAndSpec.mapHomOfTop_preimage_basicOpen _ _ _ _ _ 1 hX one_pos]
    exact Proj.isAffineOpen_basicOpen _ _ ((evalHom ℬ η hη).map_mem hX) one_pos
  dsimp only [projToProjectiveSpace]
  infer_instance

/-- The morphism defined by homogeneous parameters is compatible with the structure morphisms:
over `Spec K` it is the structure morphism of `Proj B` to `Spec B₀` followed by `K → B₀`. -/
theorem projToProjectiveSpace_comp_projToSpecCoeff :
    projToProjectiveSpace ℬ hD η hη hcov ≫ projToSpecCoeff K n =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (ℬ 0))) := by
  let := veroneseGradingGradedRing ℬ D hD
  have hV := veroneseProjIso_hom_toSpecZero ℬ D hD
  rw [projToProjectiveSpace, projToSpecCoeff_eq, Category.assoc,
    RelativeProj.mapHomOfTop_toSpecZero_assoc, reassoc_of% hV, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 3
  ext c
  simp [RelativeProj.coe_zeroHom_apply, coe_veroneseZeroHom,
    SetLike.GradeZero.coe_algebraMap, evalHom_C, veroneseConst]

end Projection

/-! ### Closed subschemes of projective space -/

section Ambient

open Stacks.ClosedSubschemeProjQuotient Stacks.RingTheory.HomogeneousQuotient

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type u} [Field K] {N : ℕ} {X : Scheme.{u}}
  (ι : X ⟶ AlgebraicGeometry.Proj (polyGrading K N)) [IsClosedImmersion ι]

/-- The inclusion of `Proj` of the homogeneous coordinate ring of a closed subscheme of `ℙᴺ` is
compatible with the structure morphisms to `Spec K`. -/
theorem ambientHom_comp_projToSpecCoeff :
    ambientHom (polyGrading K N) ι ≫ projToSpecCoeff K N =
      Proj.toSpecZero (quotientGrading _ (homogeneousIdealOfClosedSubscheme _ ι)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap K _)) := by
  rw [ambientHom, projToSpecCoeff_eq,
    Stacks.AlgebraicGeometry.RelativeProj.mapHomOfTop_toSpecZero_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  congr 3
  ext c
  simp [Stacks.AlgebraicGeometry.RelativeProj.coe_zeroHom_apply,
    SetLike.GradeZero.coe_algebraMap, quotientMk_apply]
  rfl

/-- Projective space is a Noetherian topological space. -/
theorem noetherianSpace_proj (K : Type u) [Field K] (N : ℕ) :
    TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Proj (polyGrading K N)) := by
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff K N
  have : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading K N)) :=
    LocallyOfFiniteType.isLocallyNoetherian (projToSpecCoeff K N)
  have : CompactSpace (AlgebraicGeometry.Proj (polyGrading K N)) :=
    QuasiCompact.compactSpace_of_compactSpace (projToSpecCoeff K N)
  have : IsNoetherian (AlgebraicGeometry.Proj (polyGrading K N)) := {}
  infer_instance

end Ambient

end NoetherNormalization

open MMP.ProjectiveSpace.NoetherNormalization

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **Noether normalization for projective schemes.** Let `X` be a closed subscheme of
projective space `ℙᴺ_K` over a field `K` (for instance a projective variety), of dimension `n`,
through the closed immersion `ι`. Then there is a finite surjective morphism `f : X ⟶ ℙⁿ_K` over
`K`. -/
theorem exists_isFinite_surjective {K : Type u} [Field K] {X : Scheme.{u}} {N : ℕ}
    (ι : X ⟶ AlgebraicGeometry.Proj (polyGrading K N)) [IsClosedImmersion ι] {n : ℕ}
    (hX : topologicalKrullDim X = n) :
    ∃ f : X ⟶ AlgebraicGeometry.Proj (polyGrading K n),
      IsFinite f ∧ Surjective f ∧ f ≫ projToSpecCoeff K n = ι ≫ projToSpecCoeff K N := by
  classical
  let 𝒮 := polyGrading K N
  let ℬ := Stacks.RingTheory.HomogeneousQuotient.quotientGrading 𝒮
    (Stacks.ClosedSubschemeProjQuotient.homogeneousIdealOfClosedSubscheme 𝒮 ι)
  let e : X ≅ AlgebraicGeometry.Proj ℬ :=
    Stacks.ProjQuotientFiniteCover.projectiveSpace_projQuotientIso K (N + 1) ι
  have he : e.hom ≫ Stacks.ClosedSubschemeProjQuotient.ambientHom 𝒮 ι = ι :=
    Stacks.ProjQuotientFiniteCover.projectiveSpace_projQuotientIso_hom_comp_ambientHom K (N + 1) ι
  have hdimP : topologicalKrullDim (AlgebraicGeometry.Proj ℬ) = n := by
    rwa [← IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph]
  have := noetherianSpace_proj K N
  have : TopologicalSpace.NoetherianSpace (AlgebraicGeometry.Proj ℬ) :=
    haveI := Stacks.ClosedSubschemeProjQuotient.isClosedImmersion_ambientHom 𝒮 ι
    (Stacks.ClosedSubschemeProjQuotient.ambientHom 𝒮 ι).isClosedEmbedding.isInducing.noetherianSpace
  obtain ⟨D, hD, η, hη, hcov⟩ := exists_homogeneous_family ℬ hdimP.le
  set g := projToProjectiveSpace ℬ hD η hη hcov with hg
  have : IsAffineHom g := isAffineHom_projToProjectiveSpace ℬ hD η hη hcov
  have hover : (e.hom ≫ g) ≫ projToSpecCoeff K n = ι ≫ projToSpecCoeff K N :=
    calc (e.hom ≫ g) ≫ projToSpecCoeff K n
        = e.hom ≫ (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (algebraMap K (ℬ 0)))) := by
          rw [Category.assoc, hg, projToProjectiveSpace_comp_projToSpecCoeff]
      _ = e.hom ≫ Stacks.ClosedSubschemeProjQuotient.ambientHom 𝒮 ι ≫ projToSpecCoeff K N := by
          rw [ambientHom_comp_projToSpecCoeff]
      _ = ι ≫ projToSpecCoeff K N := by
          rw [reassoc_of% he]
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff K n
  have := Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff K N
  have : IsProper ((e.hom ≫ g) ≫ projToSpecCoeff K n) := by
    rw [hover]
    infer_instance
  have : IsProper (e.hom ≫ g) := IsProper.of_comp _ (projToSpecCoeff K n)
  have : IsFinite (e.hom ≫ g) := by
    rw [IsFinite.eq_isProper_inf_isAffineHom]
    exact ⟨inferInstance, inferInstance⟩
  have := Stacks.AlgebraicGeometry.ProjPolyChart.isIntegral_proj K n
  refine ⟨e.hom ≫ g, inferInstance, surjective_of_isFinite _ hX ?_, hover⟩
  simpa using Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin K (Nat.succ_pos n)

end MMP.ProjectiveSpace
