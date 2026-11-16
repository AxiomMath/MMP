module

public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldBadBranchCount
import MMP.AlgebraicGeometry.MMP.Fourfold.PreparedChainDifficulty
import MMP.AlgebraicGeometry.MMP.Abundance.ComplementedNefThreefold
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
import MMP.AlgebraicGeometry.Resolution.Surface.PointBlowupCurvePullback
import MMP.AlgebraicGeometry.Variety.Subvariety

/-!
# The bad branch count as a sum of branch numbers

Let `(Y⁻, Θ⁻) ⤏ (Y⁺, Θ⁺)` be a small terminal flip move of a prepared chain, written as a
threefold step diagram `Y⁻ → Z ← Y⁺` with both maps small and bad loci `W^±`, and let `S_h` be a
label with centres the prime divisors `S_h^±` of `Y^±`; then `S_h^+` is the strict transform of
`S_h^-`. For `ε ∈ {-, +}`, the bad branch count
`e^ε`, the number of prime divisors `P` of the normalization `(S_h^ε)^ν` with `ν^ε(P) ⊆ W^ε`, is
the sum `∑_{C ⊆ W^ε} r^ε_{C,h}` of the branch numbers of `S_h^ε` over the irreducible curves
`C ⊆ W^ε`, a finite sum.

## Main results

* `MMP.Fourfold.StabilizedTail.PreparedChain.badBranchCount_eq_finsum_branchNumber`: on both
  sides of a flip move, the label centre on `Y⁺` is the strict transform of the one on `Y⁻`, and
  the bad branch count of a label is the finite sum of its branch numbers
  along the irreducible curves of the bad locus.

## Implementation notes

* Irreducible curves of the projective model `Y^ε` are proper curves `MMP.Mori.ProperCurve`,
  recorded by their generic points `γ`, the curve being `closure {γ}`, as in
  `MMP.Fourfold.StabilizedTail.TerminalChain.IsLabelBranchNumber`. The branch number of the
  label centre `S_h^ε` along `C` is `MMP.Fourfold.branchNumber`. The sum is the finitely
  supported sum `∑ᶠ`, and its finiteness is part of the statement: the curves contained in `W^ε`
  are finitely many.
* The proof. The normalization `ν : (S_h^ε)^ν ⟶ S_h^ε ⊆ Y^ε` is finite, so it maps each prime
  divisor `P` of the surface `(S_h^ε)^ν` onto an irreducible curve `ν(P)`; sorting the `P` with
  `ν(P) ⊆ W^ε` by this curve writes their number as the sum of the branch numbers. Every point
  of `W^ε` has codimension at least two, since both maps of the step diagram are small, proper
  and birational onto a normal base, hence isomorphisms over the points of codimension at most
  one; so the curves in `W^ε` are among its finitely many irreducible components. For the strict
  transform, `f⁻` is an isomorphism at the generic point of `S_h^-`, whose image is the generic
  point of a prime divisor `Q` of `Z`; the prime divisor of `Y⁺` over `Q` has the same valuation
  of `ℂ(Z)` as `S_h^-`, which is the valuation of the label, so it is the centre `S_h^+`.
-/

@[expose] public section

namespace MMP.Fourfold.StabilizedTail.PreparedChain

open CategoryTheory AlgebraicGeometry TopologicalSpace Order

/-! ### Dimensions of closures of points -/

/-- The closure of a point of a scheme has dimension the height of the point. -/
private theorem topologicalKrullDim_closure_singleton_eq_height {X : Scheme.{0}} (x : X) :
    topologicalKrullDim (closure {x} : Set X) = height x := by
  let T : Set X := closure {x}
  have hTc : IsClosed T := isClosed_closure
  haveI : QuasiSober T := hTc.isClosedEmbedding_subtypeVal.quasiSober
  have hpre : (specializationOrder T).toPreorder = (inferInstance : Preorder T) :=
    Preorder.ext fun a b => (Topology.IsInducing.subtypeVal.specializes_iff (x := b) (y := a)).symm
  have hheight : ∀ a : T, height a = height (a : X) := by
    refine height_eq_of_strictMono _ (Subtype.strictMono_coe _) fun a b hb => ?_
    have hbT : b ∈ T := (Scheme.le_iff_specializes.mp hb.le).mem_closed hTc a.2
    exact ⟨⟨b, hbT⟩, hb, rfl⟩
  have hx : x ∈ T := subset_closure rfl
  change krullDim (IrreducibleCloseds T) = _
  rw [@Order.krullDim_eq_of_orderIso _ _ _ (specializationOrder T).toPreorder
    irreducibleSetEquivPoints, hpre,
    krullDim_eq_iSup_height]
  refine le_antisymm (iSup_le fun a => ?_) (le_iSup_of_le ⟨x, hx⟩ ?_)
  · rw [hheight a]
    exact WithBot.coe_le_coe.mpr (height_mono (Scheme.le_iff_specializes.mpr
      (specializes_iff_mem_closure.mpr a.2)))
  · rw [hheight ⟨x, hx⟩]

/-- A finite morphism preserves heights in the specialization order. -/
private theorem height_apply_eq_of_isFinite {X Y : Scheme.{0}} (g : X ⟶ Y) [IsFinite g]
    (x : X) : height (g x) = height x := by
  have hmono : StrictMono g := fun a b hab => by
    have hba : b ⤳ a := Scheme.le_iff_specializes.mp hab.le
    refine lt_of_le_not_ge (Scheme.le_iff_specializes.mpr (hba.map g.continuous)) fun h => ?_
    have heq : g b = g a := ((hba.map g.continuous).antisymm (Scheme.le_iff_specializes.mp h)).eq
    exact hab.ne (MMP.Fourfold.eq_of_specializes_of_isFinite g hba heq).symm
  refine (height_eq_of_strictMono g hmono (fun a b hb => ?_) x).symm
  obtain ⟨a', ha', rfl⟩ := g.isClosedMap.specializingMap (Scheme.le_iff_specializes.mp hb.le)
  refine ⟨a', lt_of_le_not_ge (Scheme.le_iff_specializes.mpr ha') fun h => hb.ne ?_, rfl⟩
  rw [(Specializes.antisymm ha' (Scheme.le_iff_specializes.mp h)).eq]

/-- A finite morphism preserves the dimension of the closure of a point. -/
private theorem topologicalKrullDim_closure_image_singleton_eq {X Y : Scheme.{0}} (g : X ⟶ Y)
    [IsFinite g] (x : X) :
    topologicalKrullDim (closure {g x} : Set Y) = topologicalKrullDim (closure {x} : Set X) := by
  rw [topologicalKrullDim_closure_singleton_eq_height,
    topologicalKrullDim_closure_singleton_eq_height, height_apply_eq_of_isFinite]

/-- Cancelling `1` in `a + 1 = m + 1` in `WithBot ℕ∞`. -/
private theorem withBot_add_one_eq_natCast_succ {a : WithBot ℕ∞} {m : ℕ}
    (h : a + 1 = ((m + 1 : ℕ) : WithBot ℕ∞)) : a = m := by
  induction a using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add] at h
    exact absurd h WithBot.bot_ne_coe
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : (((⊤ + 1 : ℕ∞)) : WithBot ℕ∞) = ((m + 1 : ℕ) : ℕ∞) := h
      rw [top_add] at h'
      exact absurd (WithBot.coe_injective h').symm (ENat.coe_ne_top _)
    | coe e =>
      have h' : ((e + 1 : ℕ) : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞) := by
        rw [← h]
        norm_cast
      have : e + 1 = m + 1 := by exact_mod_cast h'
      norm_cast
      omega

/-- On an integral scheme locally of finite type over a field, a prime divisor has codimension
one: its dimension plus one is the dimension of the scheme. -/
private theorem topologicalKrullDim_support_add_one {k : Type} [Field k] {X : Scheme.{0}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] [LocallyOfFiniteType sX]
    (P : MMP.Mori.PrimeDivisor X) :
    topologicalKrullDim (P.support : Set X) + 1 = topologicalKrullDim X := by
  let _ : X.Over (Spec (.of k)) := ⟨sX⟩
  have : LocallyOfFiniteType (X ↘ Spec (.of k)) := inferInstanceAs (LocallyOfFiniteType sX)
  have h := MMP.Intersection.Scheme.Subvariety.dim_add_codim k
    (MMP.Intersection.Scheme.Subvariety.ofPoint P.genericPoint)
  rw [MMP.Intersection.Scheme.Subvariety.dim_eq_topologicalKrullDim_support,
    MMP.Intersection.Scheme.Subvariety.support_ofPoint,
    MMP.Intersection.Scheme.Subvariety.codim_eq_coheight_genericPoint,
    MMP.Intersection.Scheme.Subvariety.genericPoint_ofPoint, P.coheight_genericPoint] at h
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact_mod_cast h

/-- The closed subscheme `{x}⁻` has the dimension of the closure of `x`. -/
private theorem topologicalKrullDim_curveSubschemeAt {X : Scheme.{0}} (x : X) :
    topologicalKrullDim (MMP.Mori.curveSubschemeAt x) =
      topologicalKrullDim (closure {x} : Set X) := by
  have hrange : Set.range (MMP.Mori.curveSubschemeAtι x) = closure ({x} : Set X) := by
    change Set.range (Scheme.IdealSheafData.vanishingIdeal _).subschemeι = _
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  rw [← hrange]
  exact (MMP.Mori.curveSubschemeAtι x).isClosedEmbedding.isEmbedding.toHomeomorph
    |>.isHomeomorph.topologicalKrullDim_eq

/-! ### Counting prime divisors of the normalization -/

/-- Counting a preimage fibrewise: when every fibre of `f` is finite, the number of points
over `s` is the finitely supported sum over `s` of the fibre cardinalities. -/
private theorem ncard_preimage_eq_finsum_ncard {α β : Type*} (f : α → β) (s : Set β)
    (hfib : ∀ b, (f ⁻¹' {b}).Finite) :
    (f ⁻¹' s).ncard = ∑ᶠ (b) (_ : b ∈ s), (f ⁻¹' {b}).ncard := by
  classical
  have hsupp : s ∩ Function.support (fun b => (f ⁻¹' {b}).ncard) = f '' (f ⁻¹' s) := by
    ext b
    simp only [Set.mem_inter_iff, Function.mem_support, ne_eq, Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨hb, hne⟩
      obtain ⟨a, ha⟩ := Set.nonempty_of_ncard_ne_zero hne
      exact ⟨a, (show f a = b from ha) ▸ hb, ha⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨ha, (Set.ncard_pos (hfib _)).mpr ⟨a, rfl⟩ |>.ne'⟩
  by_cases h : (f ⁻¹' s).Finite
  · rw [finsum_mem_eq_sum_of_inter_support_eq _ (t := h.toFinset.image f)
      (by rw [Finset.coe_image, h.coe_toFinset, ← hsupp, Set.inter_assoc, Set.inter_self]),
      Set.ncard_eq_toFinset_card _ h, Finset.card_eq_sum_card_image f h.toFinset]
    refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
    have ha' : f a ∈ s := (Set.Finite.mem_toFinset h).mp ha
    rw [← Set.ncard_coe_finset]
    congr 1
    ext a'
    simp only [Finset.coe_filter, Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_setOf_eq,
      Set.mem_singleton_iff]
    exact ⟨fun h' => h'.2, fun h' => ⟨h' ▸ ha', h'⟩⟩
  · rw [Set.Infinite.ncard h, finsum_mem_eq_zero_of_infinite]
    rw [hsupp]
    exact fun hfin => h ((hfin.biUnion fun b _ => hfib b).subset fun a ha =>
      Set.mem_biUnion (Set.mem_image_of_mem f ha) rfl)

/-- The normalization of a prime divisor of a scheme locally of finite type over a field is
finite. -/
private theorem isFinite_primeDivisorNormalization {k : Type} [Field k] {Y : Scheme.{0}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (S : MMP.Mori.PrimeDivisor Y) :
    IsFinite (primeDivisorNormalization S) := by
  have := S.integral
  have : IsFinite (Stacks.AlgebraicGeometry.Normalization.normalization S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)) :=
    isFinite_normalization_of_locallyOfFiniteType S.idealSheaf.subscheme
      (S.idealSheaf.subschemeι ≫ sY) _
  infer_instance

/-- The normalization of a prime divisor maps the generic point to the generic point. -/
private theorem primeDivisorNormalization_genericPoint {Y : Scheme.{0}}
    (S : MMP.Mori.PrimeDivisor Y) :
    letI := S.integral
    letI : IsIntegral (primeDivisorNormalizationScheme S) :=
      AlgebraicGeometry.Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
    primeDivisorNormalization S (genericPoint (primeDivisorNormalizationScheme S)) =
      S.genericPoint := by
  letI := S.integral
  letI : IsIntegral (primeDivisorNormalizationScheme S) :=
    AlgebraicGeometry.Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hz : genericPoint (primeDivisorNormalizationScheme S) ∈
      genericPoints (primeDivisorNormalizationScheme S) := by
    rw [genericPoints_eq_singleton]
    rfl
  have h := Scheme.normalization_mem_genericPoints S.idealSheaf.subscheme
    (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U) hz
  rw [genericPoints_eq_singleton] at h
  change S.idealSheaf.subschemeι _ = S.idealSheaf.subschemeι _
  congr 1

/-- The image `ν(P)` of every prime divisor `P` of the normalization `S^ν` of a prime divisor `S`
of an integral scheme `Y` of finite type over a field, of dimension `n + 2`, has dimension `n`. -/
private theorem topologicalKrullDim_closure_primeDivisorNormalization_genericPoint {k : Type}
    [Field k] {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY]
    (n : ℕ) (hY : topologicalKrullDim Y = (n + 2 : ℕ)) (S : MMP.Mori.PrimeDivisor Y)
    (P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S)) :
    topologicalKrullDim (closure {primeDivisorNormalization S P.genericPoint} : Set Y) = n := by
  have := S.integral
  have := isFinite_primeDivisorNormalization sY S
  haveI : IsIntegral (primeDivisorNormalizationScheme S) :=
    AlgebraicGeometry.Scheme.isIntegral_normalizationScheme S.idealSheaf.subscheme
      (fun U _ => finite_irreducibleComponents_opens_of_irreducibleSpace U)
  have hN : topologicalKrullDim (primeDivisorNormalizationScheme S) = (n + 1 : ℕ) := by
    have hS := topologicalKrullDim_support_add_one sY S
    rw [hY] at hS
    have hgen : closure {genericPoint (primeDivisorNormalizationScheme S)} = Set.univ :=
      (genericPoint_spec (primeDivisorNormalizationScheme S)).def
    rw [← (Homeomorph.Set.univ
        (primeDivisorNormalizationScheme S)).isHomeomorph.topologicalKrullDim_eq,
      ← hgen, ← topologicalKrullDim_closure_image_singleton_eq (primeDivisorNormalization S),
      primeDivisorNormalization_genericPoint, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact withBot_add_one_eq_natCast_succ hS
  have hP := topologicalKrullDim_support_add_one (primeDivisorNormalization S ≫ sY) P
  rw [hN, AlgebraicGeometry.PrimeDivisor.support_eq_closure] at hP
  rw [topologicalKrullDim_closure_image_singleton_eq]
  exact withBot_add_one_eq_natCast_succ hP

/-! ### Curves on a proper threefold -/

section Curves

variable {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [LocallyOfFiniteType sY]

/-- On a proper scheme, a point whose closure has dimension one is the generic point of a proper
curve. -/
private theorem isProperCurve_of_topologicalKrullDim [IsProper sY] {x : Y}
    (h : topologicalKrullDim (closure {x} : Set Y) = 1) : MMP.Mori.IsProperCurve sY x :=
  MMP.Mori.isProperCurve_of_isProper sY (by rwa [topologicalKrullDim_curveSubschemeAt])

/-- On a threefold, the generic point of a proper curve has coheight two. -/
private theorem coheight_point_eq_two (hY : topologicalKrullDim Y = 3)
    (γ : MMP.Mori.ProperCurve sY) : coheight γ.point = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY γ.point
  rw [← topologicalKrullDim_curveSubschemeAt, γ.dim_eq, hY] at h
  have h' : (1 + coheight γ.point : ℕ∞) = 1 + 2 := WithBot.coe_injective (by push_cast; exact h)
  exact (WithTop.add_left_inj ENat.one_ne_top).mp h'

/-- **Finitely many curves in a closed set of codimension two.** On a threefold `Y` of finite
type over `ℂ`, a closed subset `W` all of whose points have coheight at least two contains only
finitely many proper curves: each is an irreducible component of `W`. -/
private theorem finite_setOf_closure_subset [IsProper sY] (hY : topologicalKrullDim Y = 3)
    {W : Set Y} (hW : IsClosed W) (h2 : ∀ y ∈ W, 2 ≤ coheight y) :
    {γ : MMP.Mori.ProperCurve sY | closure {γ.point} ⊆ W}.Finite := by
  haveI : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  haveI : IsNoetherian Y := ⟨⟩
  obtain ⟨S, hSf, hSc, hSi, hWS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hW
  let g : S → Y := fun t => (hSi t t.2).genericPoint
  haveI : Finite S := hSf.to_subtype
  refine ((Set.finite_range g).preimage
    (fun γ _ γ' _ => MMP.Mori.ProperCurve.ext)).subset fun γ hγ => ?_
  change closure {γ.point} ⊆ W at hγ
  obtain ⟨t, htS, hγt⟩ : ∃ t ∈ S, closure {γ.point} ⊆ t := by
    classical
    obtain ⟨t, ht, hsub⟩ := (isIrreducible_iff_sUnion_isClosed.mp
      isIrreducible_singleton.closure) hSf.toFinset
      (fun t ht => hSc t (hSf.mem_toFinset.mp ht)) (by rwa [hSf.coe_toFinset, ← hWS])
    exact ⟨t, hSf.mem_toFinset.mp ht, hsub⟩
  refine ⟨⟨t, htS⟩, ?_⟩
  have hgen := (hSi t htS).isGenericPoint_genericPoint_closure
  rw [(hSc t htS).closure_eq] at hgen
  have hspec : g ⟨t, htS⟩ ⤳ γ.point :=
    hgen.specializes (hγt (subset_closure rfl))
  have hmem : g ⟨t, htS⟩ ∈ W := hWS ▸ Set.mem_sUnion_of_mem hgen.mem htS
  by_contra hne
  have hlt : γ.point < g ⟨t, htS⟩ :=
    lt_of_le_not_ge (Scheme.le_iff_specializes.mpr hspec) fun h =>
      hne (hspec.antisymm (Scheme.le_iff_specializes.mp h)).eq
  have h3 := Order.coheight_add_one_le hlt
  rw [coheight_point_eq_two sY hY γ] at h3
  exact lt_irrefl _ ((ENat.add_one_le_iff (ne_top_of_le_ne_top (ENat.coe_ne_top 2)
    (le_self_add.trans h3))).mp (h3.trans (h2 _ hmem)))

/-- **Bad branch counts as sums of branch numbers.** For a prime divisor `S` of a proper
threefold `Y` of finite type over `ℂ` and a subset `W ⊆ Y`, the number of prime divisors `P` of
the normalization `ν : S^ν ⟶ S ⊆ Y` with `ν(P) ⊆ W` is the sum, over the proper curves `C ⊆ W`,
of the branch numbers of `S` along `C`. -/
private theorem badBranchCount_eq_finsum_branchNumber_of_dim [IsProper sY]
    (hY : topologicalKrullDim Y = 3) (S : MMP.Mori.PrimeDivisor Y) (W : Set Y) :
    badBranchCount S W = ∑ᶠ (γ : MMP.Mori.ProperCurve sY) (_ : closure {γ.point} ⊆ W),
      branchNumber S (closure {γ.point}) := by
  have := S.integral
  have := isFinite_primeDivisorNormalization sY S
  let ν := primeDivisorNormalization S
  let img : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) →
      MMP.Mori.ProperCurve sY := fun P =>
    ⟨ν P.genericPoint, isProperCurve_of_topologicalKrullDim sY
      (topologicalKrullDim_closure_primeDivisorNormalization_genericPoint sY 1 (by rw [hY]; rfl)
        S P)⟩
  have himg : ∀ P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S),
      ν '' P.support = closure {(img P).point} := fun P => by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      ← ν.isClosedMap.closure_image_eq_of_continuous ν.continuous, Set.image_singleton]
  have hclosure : ∀ a b : Y, closure ({a} : Set Y) = closure {b} ↔ a = b := fun a b =>
    ⟨fun h => (inseparable_iff_closure_eq.mpr h).eq, fun h => h ▸ rfl⟩
  have hfib : ∀ γ, (img ⁻¹' {γ}).Finite := fun γ =>
    (Set.Finite.preimage AlgebraicGeometry.PrimeDivisor.genericPoint_injective.injOn
      (ν.finite_preimage_singleton γ.point)).subset fun P hP => by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hP ⊢
      rw [← hP]
  have hbad : {P : MMP.Mori.PrimeDivisor (primeDivisorNormalizationScheme S) |
      primeDivisorNormalization S '' P.support ⊆ W} =
      img ⁻¹' {γ | closure {γ.point} ⊆ W} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    rw [himg P]
  have hbranch : ∀ γ : MMP.Mori.ProperCurve sY,
      branchNumber S (closure {γ.point}) = (img ⁻¹' {γ}).ncard := by
    intro γ
    rw [branchNumber]
    congr 1
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Set.mem_singleton_iff]
    rw [himg P, hclosure]
    exact ⟨MMP.Mori.ProperCurve.ext, fun h => h ▸ rfl⟩
  rw [badBranchCount, hbad, ncard_preimage_eq_finsum_ncard img _ hfib]
  simp only [Set.mem_setOf_eq, hbranch]

end Curves

/-! ### Points of the bad loci have codimension at least two -/

section BadLocus

open MMP.Mori

/-- Precomposing with an isomorphism does not shrink the biregular locus. -/
private theorem biregularLocus_le_biregularLocus_comp {A X Y : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (f : X ⟶ Y) : biregularLocus f ≤ biregularLocus (φ ≫ f) :=
  sSup_le fun V hV => le_biregularLocus (by
    have : IsIso (f ∣_ V) := hV
    change IsIso ((φ ≫ f) ∣_ V)
    rw [morphismRestrict_comp]
    have h2 : IsIso (φ ∣_ (f ⁻¹ᵁ V)) := by infer_instance
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h2 this)

/-- A small morphism onto a normal scheme is an isomorphism over the points of codimension at
most one: every point outside its biregular locus has coheight at least two. -/
private theorem two_le_coheight_of_notMem_biregularLocus {X Z : Scheme.{0}} [IsIntegral X]
    [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z] {sX : X ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {g : X ⟶ Z} (hg : IsSmallMorphism sX sZ g) {z : Z}
    (hz : z ∉ biregularLocus g) : 2 ≤ coheight z := by
  haveI := hg.isProper
  haveI := hg.isBirationalMorphism.isDominant
  by_contra h
  exact hz (MMP.Positivity.mem_biregularLocus_of_coheight_le_one g
    hg.isBirationalMorphism.functionFieldMap_bijective hg.two_le_codimension
    (Order.le_of_lt_add_one (not_le.mp h)))

/-- A point `y` of `X` mapping into a set of points of coheight at least two under `φ ≫ g`, with
`φ` an isomorphism and `g` of exceptional set of codimension at least two, has coheight at least
two. -/
private theorem two_le_coheight_of_comp_mem {A X Z : Scheme.{0}} (φ : A ⟶ X) [IsIso φ]
    (g : X ⟶ Z) (hg : 2 ≤ closedsCodimension (exceptionalSet g)) {T : Set Z}
    (hT : ∀ z ∈ T, 2 ≤ coheight z) {y : A} (hy : (φ ≫ g) y ∈ T) : 2 ≤ coheight y := by
  rw [← Topology.IsOpenEmbedding.coheight_eq _ φ.isOpenEmbedding]
  by_cases hb : g (φ y) ∈ biregularLocus g
  · rw [← MMP.Positivity.coheight_map_of_mem_biregularLocus g hb]
    exact hT _ hy
  · exact MMP.Positivity.two_le_coheight_of_mem_exceptionalSet hg (mem_exceptionalSet.mpr hb)

/-- **The bad locus of the base has codimension at least two.** For small morphisms
`f⁻ : X⁻ ⟶ Z` and `g : X⁺ ⟶ Z` onto a normal scheme and `f⁺ = φ ≫ g` with `φ` an isomorphism,
every point of `Σ = Z ∖ U` has coheight at least two. -/
private theorem two_le_coheight_of_mem_badLocusBase {Xm Xp A Z : Scheme.{0}} [IsIntegral Xm]
    [IsIntegral Xp] [IsIntegral Z] [IsLocallyNoetherian Z] [IsNormal Z]
    {sXm : Xm ⟶ Spec (.of ℂ)} {sXp : Xp ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)} {fm : Xm ⟶ Z}
    {g : Xp ⟶ Z} (hm : IsSmallMorphism sXm sZ fm) (hp : IsSmallMorphism sXp sZ g)
    (φ : A ⟶ Xp) [IsIso φ] {z : Z} (hz : z ∈ (badLocusBase fm (φ ≫ g) : Set Z)) :
    2 ≤ coheight z := by
  rw [coe_badLocusBase, Set.mem_compl_iff, commonBiregularLocus] at hz
  by_cases h1 : z ∈ biregularLocus fm
  · exact two_le_coheight_of_notMem_biregularLocus hp fun h2 =>
      hz ⟨h1, biregularLocus_le_biregularLocus_comp φ g h2⟩
  · exact two_le_coheight_of_notMem_biregularLocus hm h1

end BadLocus

/-! ### The strict transform across a step diagram -/

section StrictTransform

variable {X Y : Scheme.{0}}

/-- A point outside the exceptional set of `f` has the same coheight as its image. -/
private theorem coheight_map_of_notMem_exceptionalSet {f : X ⟶ Y} {x : X}
    (hx : x ∉ (MMP.Mori.exceptionalSet f : Set X)) : Order.coheight (f x) = Order.coheight x := by
  set V := MMP.Mori.biregularLocus f
  have : IsIso (f ∣_ V) := MMP.Mori.isBiregular_biregularLocus f
  let q : (f ⁻¹ᵁ V).toScheme := ⟨x, not_not.mp hx⟩
  have h1 : Order.coheight (((f ∣_ V) ≫ V.ι) q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ ((f ∣_ V) ≫ V.ι).isOpenEmbedding
  have h2 : Order.coheight ((f ⁻¹ᵁ V).ι q) = Order.coheight q :=
    Topology.IsOpenEmbedding.coheight_eq _ (f ⁻¹ᵁ V).ι.isOpenEmbedding
  have h3 : ((f ∣_ V) ≫ V.ι) q = f x := by rw [morphismRestrict_ι]; rfl
  rw [← h3, h1, ← h2]
  rfl

/-- If the exceptional set of `f` has codimension at least two, it misses the generic point of
every prime divisor. -/
private theorem genericPoint_notMem_exceptionalSet {f : X ⟶ Y}
    (h2 : 2 ≤ MMP.Mori.closedsCodimension (MMP.Mori.exceptionalSet f))
    (P : MMP.Mori.PrimeDivisor X) :
    P.genericPoint ∉ (MMP.Mori.exceptionalSet f : Set X) := fun h => by
  have := MMP.Positivity.two_le_coheight_of_mem_exceptionalSet h2 h
  rw [P.coheight_genericPoint] at this
  exact absurd this (by decide)

/-- A morphism whose exceptional set has codimension at least two is biregular over the image
of the generic point of every prime divisor. -/
private theorem map_genericPoint_mem_biregularLocus {f : X ⟶ Y}
    (h2 : 2 ≤ MMP.Mori.closedsCodimension (MMP.Mori.exceptionalSet f))
    (P : MMP.Mori.PrimeDivisor X) : f P.genericPoint ∈ MMP.Mori.biregularLocus f :=
  not_not.mp (genericPoint_notMem_exceptionalSet h2 P)

/-- The valuation of a prime divisor seen through a composite. -/
private theorem valuationOver_comp {Z : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [IsIntegral Y] [IsIntegral Z] (P : MMP.Mori.PrimeDivisor X) (a : X ⟶ Y)
    (b : Y ⟶ Z) [IsDominant a] [IsDominant b] [IsDominant (a ≫ b)] :
    P.valuationOver (a ≫ b) = (P.valuationOver a).comap (functionFieldMap b) :=
  Valuation.ext fun t => by
    simp only [Valuation.comap_apply, MMP.Mori.PrimeDivisor.valuationOver_apply,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]

/-- The valuation of a prime divisor through equal dominant morphisms. -/
private theorem valuationOver_congr [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] (P : MMP.Mori.PrimeDivisor X) {a b : X ⟶ Y} [IsDominant a] [IsDominant b]
    (h : a = b) : P.valuationOver a = P.valuationOver b := by
  subst h
  rfl

/-- If `f(η_E) = η_Q` and `f^♯ : 𝒪_{Y,Q} ⟶ 𝒪_{X,E}` is an isomorphism, then `v_E`, seen on
`k(Y)` through `f`, is `v_Q`. -/
private theorem valuationOver_eq_of_isIso [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsDominant f]
    (E : MMP.Mori.PrimeDivisor X) (Q : MMP.Mori.PrimeDivisor Y)
    (heq : f E.genericPoint = Q.genericPoint) [IsIso (f.stalkMap E.genericPoint)] :
    E.valuationOver f = Q.divisorialValuation := by
  refine Valuation.ext fun t => ?_
  rw [MMP.Mori.PrimeDivisor.valuationOver_apply]
  by_cases ht : t = 0
  · rw [ht, map_zero, map_zero, map_zero]
  rw [MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ((map_ne_zero _).mpr ht),
    MMP.Mori.PrimeDivisor.divisorialValuation_eq_exp_neg_ord _ ht,
    MMP.Positivity.ord_functionFieldMap_of_isIso f E Q heq t]

/-- A proper birational morphism onto a normal scheme is an isomorphism of local rings over the
generic point of each prime divisor `Q` of the target. -/
private theorem exists_primeDivisor_isIso_stalkMap [IsIntegral X] [IsLocallyNoetherian X]
    [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y] (f : X ⟶ Y) [IsProper f]
    (hf : MMP.Mori.IsBirationalMorphism f) (Q : MMP.Mori.PrimeDivisor Y) :
    ∃ E : MMP.Mori.PrimeDivisor X,
      f E.genericPoint = Q.genericPoint ∧ IsIso (f.stalkMap E.genericPoint) := by
  have := Q.isDiscreteValuationRing_localRing
  haveI := hf.isDominant
  obtain ⟨x, hx, hiso⟩ :=
    MMP.Intersection.exists_isIso_stalkMap_of_valuationRing f hf.functionFieldMap_bijective
      Q.genericPoint
  have hco : Order.coheight x = 1 := by
    have h := ringKrullDim_eq_of_ringEquiv (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight, hx,
      Q.coheight_genericPoint] at h
    exact_mod_cast h.symm
  let E : MMP.Mori.PrimeDivisor X := AlgebraicGeometry.PrimeDivisor.ofCoheightOne x hco
  have hE : E.genericPoint = x := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne x hco
  exact ⟨E, hE ▸ hx, hE ▸ hiso⟩

/-- A prime divisor on the target of an isomorphism of schemes is the image of one on its
source. -/
private theorem exists_primeDivisor_map_genericPoint_eq_of_isIso {A X : Scheme.{0}}
    (φ : A ⟶ X) [IsIso φ] (P : MMP.Mori.PrimeDivisor X) :
    ∃ S : MMP.Mori.PrimeDivisor A, φ S.genericPoint = P.genericPoint := by
  have hφ : φ (inv φ P.genericPoint) = P.genericPoint := by
    rw [← Scheme.Hom.comp_apply, IsIso.inv_hom_id]
    rfl
  have hy : Order.coheight (inv φ P.genericPoint) = 1 := by
    rw [← Topology.IsOpenEmbedding.coheight_eq _ φ.isOpenEmbedding, hφ, P.coheight_genericPoint]
  let S : MMP.Mori.PrimeDivisor A := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hy
  have hS : S.genericPoint = inv φ P.genericPoint :=
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hy
  exact ⟨S, hS ▸ hφ⟩

/-- **The strict transform across a step diagram.** Let `X⁻ → Z ← X⁺` be a step diagram whose
morphism `f⁻` is small, and let `f : A ⟶ Z` be `f⁺` precomposed with an isomorphism
`φ : A ⟶ X⁺`. Every prime divisor `S` of `X⁻` has a strict transform `S⁺ = f⁻¹_* f⁻_* S` on `A`,
and `ord_{S⁺} = ord_S` as valuations of `k(Z)`. -/
private theorem exists_flipTransformPrimeDivisor_eq_some {Xm Xp Z A : Scheme.{0}}
    [IsIntegral Xm] [CompactSpace Xm] [IsLocallyNoetherian Xm] [IsNormal Xm] [IsIntegral Xp]
    [CompactSpace Xp] [IsLocallyNoetherian Xp] [IsNormal Xp] [IsIntegral A]
    [IsLocallyNoetherian A] [IsNormal A] {sXm : Xm ⟶ Spec (.of ℂ)} {sZ : Z ⟶ Spec (.of ℂ)}
    {sXp : Xp ⟶ Spec (.of ℂ)} {K : MMP.Mori.Divisor Xm} {B : MMP.Mori.QDivisor Xm}
    {fm : Xm ⟶ Z} {fp : Xp ⟶ Z} (hD : IsThreefoldStepDiagram sXm sZ sXp K B fm fp)
    (hsm : IsSmallMorphism sXm sZ fm) (f : A ⟶ Z) (φ : A ⟶ Xp) [IsIso φ] (hf : f = φ ≫ fp)
    (S : MMP.Mori.PrimeDivisor Xm) :
    haveI := hD.isNormalVariety_target.1.toIsIntegral
    haveI := hD.isBirationalMorphism_minus.isDominant
    ∃ (S' : MMP.Mori.PrimeDivisor A) (_ : IsDominant f),
      flipTransformPrimeDivisor fm f S = some S' ∧ S'.valuationOver f = S.valuationOver fm := by
  have hZ := hD.isNormalVariety_target
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  haveI : IsNormal Z := hZ.2
  haveI : LocallyOfFiniteType sZ := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian sZ
  haveI : IsSeparated (Z ↘ Limits.terminal Scheme) := by
    have := hZ.1
    rw [show (Z ↘ Limits.terminal Scheme) = sZ ≫ (Spec (.of ℂ) ↘ Limits.terminal Scheme) from
      Limits.terminal.hom_ext _ _]
    infer_instance
  have hbm := hD.isBirationalMorphism_minus
  have hbp := hD.isSmallMorphism_plus.isBirationalMorphism
  haveI := hbm.isDominant
  haveI := hbp.isDominant
  haveI : IsProper fp := hD.isSmallMorphism_plus.isProper
  subst hf
  have hζ : Order.coheight (fm S.genericPoint) = 1 := by
    rw [coheight_map_of_notMem_exceptionalSet
      (genericPoint_notMem_exceptionalSet hsm.two_le_codimension S),
      S.coheight_genericPoint]
  set Q : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne _ hζ
  have hQ : fm S.genericPoint = Q.genericPoint :=
    (AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne _ hζ).symm
  have := Q.isDiscreteValuationRing_localRing
  haveI : ValuationRing (Z.presheaf.stalk (fm S.genericPoint)) := by rw [hQ]; infer_instance
  haveI := MMP.Positivity.isIso_stalkMap_of_valuationRing fm hbm.functionFieldMap_bijective
    S.genericPoint
  obtain ⟨P, hPQ, hPiso⟩ := exists_primeDivisor_isIso_stalkMap fp hbp Q
  obtain ⟨S', hS'⟩ := exists_primeDivisor_map_genericPoint_eq_of_isIso φ P
  have hS'Q : (φ ≫ fp) S'.genericPoint = Q.genericPoint := by
    rw [Scheme.Hom.comp_apply, hS', hPQ]
  have hfpiso : IsIso (fp.stalkMap (φ S'.genericPoint)) := by rwa [hS']
  haveI : IsIso ((φ ≫ fp).stalkMap S'.genericPoint) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hfpiso inferInstance
  refine ⟨S', inferInstance, ?_, ?_⟩
  · unfold flipTransformPrimeDivisor
    rw [(MMP.Positivity.transformPrimeDivisor_toRationalMap_eq_some_iff fm S Q).mpr hQ,
      Option.bind_some]
    refine MMP.Threefold.Resolution.inverseTransformPrimeDivisor_eq_some_of_map_genericPoint
      hS'Q ?_
    rw [hS'Q, ← hPQ]
    exact biregularLocus_le_biregularLocus_comp φ fp
      (map_genericPoint_mem_biregularLocus hD.isSmallMorphism_plus.two_le_codimension P)
  · rw [valuationOver_eq_of_isIso _ S' Q hS'Q, valuationOver_eq_of_isIso _ S Q hQ]

end StrictTransform

/-! ### Label centres on the models of a terminal chain -/

section LabelCentre

/-- Valuations agreeing after composition with a surjective ring map agree. -/
private theorem valuation_eq_of_comap_eq {K L Γ : Type*} [CommRing K] [CommRing L]
    [LinearOrderedCommMonoidWithZero Γ] {φ : K →+* L} (hφ : Function.Surjective φ)
    {v w : Valuation L Γ} (h : v.comap φ = w.comap φ) : v = w :=
  Valuation.ext fun x => by
    obtain ⟨y, rfl⟩ := hφ x
    exact congrArg (fun u : Valuation K Γ => u y) h

/-- The transport of a valuation of `k(X_0)` to `k(X_i)` is unique. -/
private theorem isTransportedValuationFrom_unique {T : StabilizedTail} :
    ∀ (i : ℕ) {ν : Valuation (T.X 0).functionField (WithZero (Multiplicative ℤ))}
      {w w' : Valuation (T.X i).functionField (WithZero (Multiplicative ℤ))},
      T.IsTransportedValuationFrom i ν w → T.IsTransportedValuationFrom i ν w' → w = w'
  | 0, _, _, _, h, h' => h.trans h'.symm
  | i + 1, _, _, _, ⟨u, hu, h⟩, ⟨u', hu', h'⟩ => by
    obtain rfl := isTransportedValuationFrom_unique i hu hu'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    exact valuation_eq_of_comap_eq (T.isThreefoldStepDiagram
      i).isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2
      ((show _ = _ from h).trans (show _ = _ from h').symm)

/-- A prime divisor of a normal variety is determined by its valuation of `k(B)`, for a dominant
morphism `f : Y ⟶ B` inducing a surjection of function fields. -/
private theorem primeDivisor_eq_of_valuationOver_eq {Y B : Scheme.{0}} [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] [IsIntegral B] {sY : Y ⟶ Spec (.of ℂ)}
    (hY : MMP.Mori.IsNormalVariety ℂ sY) (f : Y ⟶ B) [IsDominant f]
    (hf : Function.Surjective (functionFieldMap f)) {P P' : MMP.Mori.PrimeDivisor Y}
    (h : P.valuationOver f = P'.valuationOver f) : P = P' := by
  have hv : P.divisorialValuation = P'.divisorialValuation := valuation_eq_of_comap_eq hf h
  have := MMP.Positivity.DivisorOver.map_genericPoint_eq_of_valuation_eq hY.1
    (D := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hY P)
    (D' := MMP.Mori.DivisorOver.ofPrimeDivisor ℂ hY P') (by
      change P.divisorialValuation.comap _ = P'.divisorialValuation.comap _
      rw [hv]
      rfl)
  exact AlgebraicGeometry.PrimeDivisor.genericPoint_injective this

/-- If `π : V ⟶ Z` is dominant and induces a surjection of function fields, so does every
morphism `π_k : V_k ⟶ Z`, `k ≤ m`, of a finite relative programme over `Z` from `V`. -/
private theorem surjective_functionFieldMap_modelMap_of_le {V Z : Scheme.{0}} [IsIntegral V]
    [CompactSpace V] [IsLocallyNoetherian V] [IsNormal V] {sV : V ⟶ Spec (.of ℂ)}
    {sZ : Z ⟶ Spec (.of ℂ)} {π : V ⟶ Z} [IsIntegral Z] {K : MMP.Mori.Divisor V}
    {Θ : MMP.Mori.QDivisor V}
    (P : RelativeThreefoldProgram sV sZ π K Θ) [IsDominant π]
    (hπ : Function.Surjective (functionFieldMap π)) :
    ∀ n ≤ P.m, ∃ _ : IsDominant (modelMap π P.πY n),
      Function.Surjective (functionFieldMap (modelMap π P.πY n))
  | 0, _ => ⟨‹_›, hπ⟩
  | n + 1, hn => by
    obtain ⟨hd, hs⟩ := surjective_functionFieldMap_modelMap_of_le P hπ n (by omega)
    have hD := P.isThreefoldStepDiagram n (by omega)
    haveI := hD.isNormalVariety_target.1.toIsIntegral
    haveI := hD.isBirationalMorphism_minus.isDominant
    haveI := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
    have heq := P.modelMap_eq n (by omega)
    have hpeq := P.πY_eq n (by omega)
    haveI : IsDominant (P.h n) := by
      have : IsDominant (P.g n ≫ P.h n) := heq ▸ hd
      exact IsDominant.of_comp (P.g n) (P.h n)
    change ∃ _ : IsDominant (P.πY n), Function.Surjective (functionFieldMap (P.πY n))
    haveI hd' : IsDominant (P.πY n) := hpeq ▸ (inferInstance : IsDominant (P.gp n ≫ P.h n))
    refine ⟨hd', ?_⟩
    have hh : Function.Surjective (functionFieldMap (P.h n)) := by
      refine Function.Surjective.of_comp_left ?_
        hD.isBirationalMorphism_minus.functionFieldMap_bijective.1
      have : (functionFieldMap (P.g n)) ∘ (functionFieldMap (P.h n)) =
          functionFieldMap (modelMap π P.πY n) := by
        funext t
        rw [Function.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
        exact congrArg (fun φ => φ t)
          (MMP.Positivity.DivisorOver.functionFieldMap_congr heq.symm)
      rwa [this]
    have : functionFieldMap (P.πY n) =
        (functionFieldMap (P.gp n)).comp (functionFieldMap (P.h n)) := by
      ext t
      rw [RingHom.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
      exact congrArg (fun φ => φ t) (MMP.Positivity.DivisorOver.functionFieldMap_congr hpeq)
    rw [this, RingHom.coe_comp]
    exact hD.isSmallMorphism_plus.isBirationalMorphism.functionFieldMap_bijective.2.comp hh

/-- On the model `V_k` of a bridge, the morphism `π_k : V_k ⟶ Z_i` induces a surjection of
function fields. -/
private theorem surjective_functionFieldMap_modelMap {T : StabilizedTail}
    (C : TerminalChain T) (i : ℕ) (k : Fin (C.bridge i).P.m)
    [IsIntegral (T.Z i)] [IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)] :
    Function.Surjective
      (functionFieldMap (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)) := by
  have hpb := (C.junction i).isBirationalMorphism
  have hfb := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus
  haveI := hpb.isDominant
  haveI := hfb.isDominant
  have hπ : Function.Surjective (functionFieldMap ((C.junction i).p ≫ T.f i)) := by
    have : functionFieldMap ((C.junction i).p ≫ T.f i) =
        (functionFieldMap (C.junction i).p).comp (functionFieldMap (T.f i)) := by
      ext t
      rw [RingHom.comp_apply, MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
    rw [this, RingHom.coe_comp]
    exact hpb.functionFieldMap_bijective.2.comp hfb.functionFieldMap_bijective.2
  exact (surjective_functionFieldMap_modelMap_of_le (C.bridge i).P hπ k k.2.le).2

/-- The centre of a label on a model of a terminal chain is unique. -/
private theorem isLabelCentre_unique {T : StabilizedTail} (C : TerminalChain T)
    {S : C.Label} {x : C.ModelIndex} {P P' : MMP.Mori.PrimeDivisor (C.model x)}
    (h : C.IsLabelCentre S x P) (h' : C.IsLabelCentre S x P') : P = P' := by
  rcases x with ⟨i, _ | k⟩
  · obtain ⟨w, hw, hPw⟩ := h
    obtain ⟨w', hw', hPw'⟩ := h'
    cases isTransportedValuationFrom_unique i hw hw'
    have hb := (C.junction i).isBirationalMorphism
    haveI := hb.isDominant
    exact primeDivisor_eq_of_valuationOver_eq (C.junction i).isQFactorial.1 (C.junction i).p
      hb.functionFieldMap_bijective.2 (hPw.trans hPw'.symm)
  · obtain ⟨w, hw, hdom, hPw⟩ := h
    obtain ⟨w', hw', _hdom', hPw'⟩ := h'
    cases isTransportedValuationFrom_unique i hw hw'
    haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
    exact primeDivisor_eq_of_valuationOver_eq
      ((C.bridge i).P.isQFactorial k (by omega)).1
      (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY k)
      (surjective_functionFieldMap_modelMap C i k) (hPw.trans hPw'.symm)

/-- Along an equality `a = b` of indices, the identification `V_a = V_b` of models of a
programme is compatible with the morphisms `π_a`, `π_b` to the base. -/
private theorem eqToHom_comp_modelMap {V Z : Scheme.{0}} {Y : ℕ → Scheme.{0}} (π : V ⟶ Z)
    (πY : ∀ k, Y k ⟶ Z) {a b : ℕ} (h : a = b) :
    eqToHom (congrArg (modelSeq V Y) h) ≫ modelMap π πY b = modelMap π πY a := by
  subst h
  simp

/-- When the `k`-th flip is the last move of the `i`-th bridge, the morphism from the model
reached by the flip to the next junction base factors through `h_k`. -/
private theorem junction_succ_p_comp_fp_eq {T : StabilizedTail} (C : TerminalChain T) (i : ℕ)
    (k : Fin (C.bridge i).P.m) (h : ¬ k.1 + 1 < (C.bridge i).P.m) :
    ((C.junction (i + 1)).p ≫ T.fp i : C.model (C.flipTargetOf i k (isFalse h)) ⟶ _) =
      C.flipTargetMapOf i k (isFalse h) ≫ (C.bridge i).P.h k := by
  have hmk : (C.bridge i).P.m = k.1 + 1 := by omega
  change _ = ((C.bridge i).e.inv ≫ eqToHom _ ≫ (C.bridge i).P.gp k) ≫ (C.bridge i).P.h k
  rw [Category.assoc, Category.assoc, ← (C.bridge i).P.πY_eq k k.2]
  change _ = (C.bridge i).e.inv ≫ eqToHom _ ≫
    modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY (k.1 + 1)
  rw [eqToHom_comp_modelMap, (C.bridge i).modelMap_eq, Iso.inv_hom_id_assoc]
  exacts [rfl, hmk]

/-- When the `k`-th flip is the last move of the `i`-th bridge, the morphism from the model
reached by the flip to the next junction base is dominant. -/
private theorem isDominant_junction_succ_p_comp_fp {T : StabilizedTail} (C : TerminalChain T)
    (i : ℕ) (k : Fin (C.bridge i).P.m) (h : ¬ k.1 + 1 < (C.bridge i).P.m) :
    IsDominant (X := C.model (C.flipTargetOf i k (isFalse h))) ((C.junction (i + 1)).p ≫ T.fp i) :=
  ⟨(T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant.denseRange.comp
    (C.junction (i + 1)).isBirationalMorphism.isDominant.denseRange (Scheme.Hom.continuous _)⟩

/-- **Labels across a flip of a bridge.** For the `k`-th flip `V_k → T_k ← V_{k+1}` of the `i`-th
bridge of a terminal chain and the centre `S⁻` of a label on `V_k`, the strict transform of `S⁻`
on the model reached by the flip is a prime divisor, and it is the centre of the label there. -/
private theorem exists_flipTransformPrimeDivisor_isLabelCentre {T : StabilizedTail}
    (C : TerminalChain T) (i : ℕ) (k : Fin (C.bridge i).P.m) {S : C.Label}
    {Sm : MMP.Mori.PrimeDivisor (C.model ⟨i, some k⟩)} (hm : C.IsLabelCentre S ⟨i, some k⟩ Sm) :
    ∃ Sp : MMP.Mori.PrimeDivisor (C.model (C.flipTarget i k)),
      flipTransformPrimeDivisor ((C.bridge i).P.g k) (C.flipTargetMap i k) Sm = some Sp ∧
        C.IsLabelCentre S (C.flipTarget i k) Sp := by
  have hD := (C.bridge i).P.isThreefoldStepDiagram k k.2
  have hsm := (C.bridge i).isSmallMorphism k k.2
  haveI := hD.isNormalVariety_target.1.toIsIntegral
  haveI := hD.isBirationalMorphism_minus.isDominant
  haveI := hD.isSmallMorphism_plus.isBirationalMorphism.isDominant
  haveI := (T.isThreefoldStepDiagram i).isNormalVariety_target.1.toIsIntegral
  haveI := (T.isThreefoldStepDiagram i).isBirationalMorphism_minus.isDominant
  obtain ⟨w, hw, hdom, hSm⟩ := hm
  have heq := (C.bridge i).P.modelMap_eq k k.2
  have hpeq := (C.bridge i).P.πY_eq k k.2
  haveI : IsDominant ((C.bridge i).P.h k) := by
    have : IsDominant ((C.bridge i).P.g k ≫ (C.bridge i).P.h k) := heq ▸ hdom
    exact IsDominant.of_comp ((C.bridge i).P.g k) _
  have key : ∀ {A : Scheme.{0}} [IsIntegral A] [IsLocallyNoetherian A] [IsNormal A]
      (f : A ⟶ (C.bridge i).P.T k) (φ : A ⟶ (C.bridge i).P.Y k) [IsIso φ]
      (_ : f = φ ≫ (C.bridge i).P.gp k),
      ∃ (Sp : MMP.Mori.PrimeDivisor A) (_ : IsDominant f),
        flipTransformPrimeDivisor ((C.bridge i).P.g k) f Sm = some Sp ∧
          Sp.valuationOver (f ≫ (C.bridge i).P.h k) = w.comap (functionFieldMap (T.f i)) := by
    intro A _ _ _ f φ _ hf
    obtain ⟨Sp, hd, hfl, hv⟩ := exists_flipTransformPrimeDivisor_eq_some hD hsm f φ hf Sm
    refine ⟨Sp, hd, hfl, ?_⟩
    rw [valuationOver_comp, hv]
    exact (valuationOver_comp (X := modelSeq (C.junction i).Y (C.bridge i).P.Y k) Sm _ _).symm.trans
      ((valuationOver_congr (X := modelSeq (C.junction i).Y (C.bridge i).P.Y k) Sm
        heq.symm).trans hSm)
  unfold TerminalChain.flipTarget TerminalChain.flipTargetMap
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue h =>
    obtain ⟨Sp, hd, hfl, hv⟩ := key ((C.bridge i).P.gp k) (𝟙 _) (Category.id_comp _).symm
    have hd1 : IsDominant (modelMap ((C.junction i).p ≫ T.f i) (C.bridge i).P.πY
        ((⟨k.1 + 1, h⟩ : Fin _) : ℕ)) := by
      change IsDominant ((C.bridge i).P.πY k)
      rw [hpeq]
      infer_instance
    exact ⟨Sp, hfl, w, hw, hd1, (@valuationOver_congr _ _ _ _ _ _ Sp _ _ hd1 _ hpeq).trans hv⟩
  | isFalse h =>
    let φ : C.model (C.flipTargetOf i k (isFalse h)) ≅ (C.bridge i).P.Y k :=
      (C.bridge i).e.symm ≪≫ eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y)
        (by omega : (C.bridge i).P.m = k.1 + 1))
    obtain ⟨Sp, hd, hfl, hv⟩ := key (C.flipTargetMapOf i k (isFalse h)) φ.hom
      (Category.assoc _ _ _).symm
    haveI : IsDominant (X := C.model (C.flipTargetOf i k (isFalse h))) (C.junction (i + 1)).p :=
      (C.junction (i + 1)).isBirationalMorphism.isDominant
    refine ⟨Sp, hfl, Sp.valuationOver (C.junction (i + 1)).p, ⟨w, hw, ?_⟩, rfl⟩
    haveI := (T.isThreefoldStepDiagram i).isSmallMorphism_plus.isBirationalMorphism.isDominant
    haveI := isDominant_junction_succ_p_comp_fp C i k h
    exact (valuationOver_comp (X := C.model (C.flipTargetOf i k (isFalse h))) Sp
      (C.junction (i + 1)).p (T.fp i)).symm.trans
        ((valuationOver_congr Sp (junction_succ_p_comp_fp_eq C i k h)).trans hv)

end LabelCentre

/-! ### The models and the flip moves of a prepared chain -/

section Chain

/-- Every model of a terminal chain is a threefold. -/
private theorem topologicalKrullDim_model {T : StabilizedTail} (C : TerminalChain T) :
    ∀ x : C.ModelIndex, topologicalKrullDim (C.model x) = 3
  | ⟨i, none⟩ => (C.junction i).dim_eq
  | ⟨i, some ⟨0, _⟩⟩ => (C.junction i).dim_eq
  | ⟨i, some ⟨k + 1, hk⟩⟩ =>
    ((C.bridge i).P.isThreefoldStepDiagram k (by omega)).dim_plus

/-- Every model of a terminal chain is of finite type and proper over `ℂ`. -/
private theorem locallyOfFiniteType_and_isProper_modelStructure {T : StabilizedTail}
    (C : TerminalChain T) (x : C.ModelIndex) :
    LocallyOfFiniteType (C.modelStructure x) ∧ IsProper (C.modelStructure x) := by
  have h := C.isProjectiveVariety_modelStructure x
  exact ⟨h.toLocallyOfFiniteType, isProper_of_isProjectiveMorphism _ h.isProjective⟩

/-- The morphism `Y⁺ ⟶ T_k` of a flip of a bridge is `g_k⁺` precomposed with an
isomorphism. -/
private theorem exists_isIso_flipTargetMap_eq {T : StabilizedTail} (C : TerminalChain T) (i : ℕ)
    (k : Fin (C.bridge i).P.m) :
    ∃ (φ : C.model (C.flipTarget i k) ⟶ (C.bridge i).P.Y k) (_ : IsIso φ),
      C.flipTargetMap i k = φ ≫ (C.bridge i).P.gp k := by
  unfold TerminalChain.flipTarget TerminalChain.flipTargetMap
  generalize (inferInstance : Decidable (k.1 + 1 < (C.bridge i).P.m)) = d
  cases d with
  | isTrue h => exact ⟨𝟙 ((C.bridge i).P.Y k), IsIso.id _, (Category.id_comp _).symm⟩
  | isFalse h =>
    let ψ : (C.junction (i + 1)).Y ≅ (C.bridge i).P.Y k := (C.bridge i).e.symm ≪≫
      eqToIso (congrArg (modelSeq (C.junction i).Y (C.bridge i).P.Y)
        (by omega : (C.bridge i).P.m = k.1 + 1))
    exact ⟨ψ.hom, ψ.isIso_hom, (Category.assoc _ _ _).symm⟩

end Chain

/-- **The bad loci of a flip move have codimension at least two.** Both maps of the step
diagram `Y⁻ → Z ← Y⁺` of a flip move of a prepared chain are small onto a normal base, so every
point of the bad loci `W⁻ ⊆ Y⁻` and `W⁺ ⊆ Y⁺` has coheight at least two. -/
private theorem two_le_coheight_of_mem_badLoci {T : StabilizedTail} (Q : PreparedChain T)
    (μ : Q.FlipMove) :
    (∀ y ∈ (μ.badLocusSource : Set (Q.chain.model μ.source.1)), 2 ≤ coheight y) ∧
      ∀ y ∈ (μ.badLocusTarget : Set (Q.chain.model μ.target.1)), 2 ≤ coheight y := by
  have hD := (Q.chain.bridge μ.1.1).P.isThreefoldStepDiagram μ.1.2 μ.1.2.2
  have hsm : IsSmallMorphism _ _ μ.sourceMap := (Q.chain.bridge μ.1.1).isSmallMorphism μ.1.2 μ.1.2.2
  have hsp := hD.isSmallMorphism_plus
  have hZ := hD.isNormalVariety_target
  haveI : IsNormal μ.base := hZ.2
  haveI : LocallyOfFiniteType ((Q.chain.bridge μ.1.1).P.sT μ.1.2) := hZ.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian μ.base :=
    LocallyOfFiniteType.isLocallyNoetherian ((Q.chain.bridge μ.1.1).P.sT μ.1.2)
  obtain ⟨φ, hφ, hft⟩ := exists_isIso_flipTargetMap_eq Q.chain μ.1.1 μ.1.2
  have hft' : μ.targetMap = φ ≫ (Q.chain.bridge μ.1.1).P.gp μ.1.2 := hft
  have hbase : ∀ z ∈ (badLocusBase μ.sourceMap μ.targetMap : Set μ.base), 2 ≤ coheight z :=
    fun z hz => two_le_coheight_of_mem_badLocusBase hsm hsp φ (hft' ▸ hz)
  exact ⟨fun y hy => two_le_coheight_of_comp_mem (𝟙 _) μ.sourceMap hsm.two_le_codimension hbase
      (by rwa [Category.id_comp]),
    fun y hy => two_le_coheight_of_comp_mem φ _ hsp.two_le_codimension hbase
      (by rwa [← hft'])⟩

/-- **The bad branch count is a sum of branch numbers.** For a small terminal flip move
`Y⁻ → Z ← Y⁺` of a prepared chain, with bad loci `W^±`, and a label `S_h` with centres the prime
divisors `S_h^±` of `Y^±`, the strict transform of `S_h^-` is `S_h^+`, and for `ε ∈ {-, +}`
the curves `C ⊆ W^ε` are finitely many and the bad branch count
`e^ε(S_h^-) = #{P ⊆ (S_h^ε)^ν : ν^ε(P) ⊆ W^ε}` is `∑_{C ⊆ W^ε} r^ε_{C,h}`. -/
@[mmp "lem_mmp_indexd_bad_branch_count_sum"]
theorem badBranchCount_eq_finsum_branchNumber {T : StabilizedTail} (Q : PreparedChain T)
    (μ : Q.FlipMove) (S : Q.chain.Label)
    (Pm : MMP.Mori.PrimeDivisor (Q.chain.model μ.source.1))
    (Pp : MMP.Mori.PrimeDivisor (Q.chain.model μ.target.1))
    (hm : Q.chain.IsLabelCentre S μ.source.1 Pm) (hp : Q.chain.IsLabelCentre S μ.target.1 Pp) :
    ({γ : MMP.Mori.ProperCurve (Q.chain.modelStructure μ.source.1) |
        closure {γ.point} ⊆ (μ.badLocusSource : Set (Q.chain.model μ.source.1))}.Finite ∧
      badBranchCount Pm μ.badLocusSource =
        ∑ᶠ (γ : MMP.Mori.ProperCurve (Q.chain.modelStructure μ.source.1))
          (_ : closure {γ.point} ⊆ (μ.badLocusSource : Set (Q.chain.model μ.source.1))),
          branchNumber Pm (closure {γ.point})) ∧
    (flipTransformPrimeDivisor μ.sourceMap μ.targetMap Pm = some Pp ∧
      {γ : MMP.Mori.ProperCurve (Q.chain.modelStructure μ.target.1) |
        closure {γ.point} ⊆ (μ.badLocusTarget : Set (Q.chain.model μ.target.1))}.Finite ∧
      badBranchCount Pp μ.badLocusTarget =
        ∑ᶠ (γ : MMP.Mori.ProperCurve (Q.chain.modelStructure μ.target.1))
          (_ : closure {γ.point} ⊆ (μ.badLocusTarget : Set (Q.chain.model μ.target.1))),
          branchNumber Pp (closure {γ.point})) := by
  obtain ⟨hcohm, hcohp⟩ := two_le_coheight_of_mem_badLoci Q μ
  obtain ⟨hlm, hpm⟩ := locallyOfFiniteType_and_isProper_modelStructure Q.chain μ.source.1
  obtain ⟨hlp, hpp⟩ := locallyOfFiniteType_and_isProper_modelStructure Q.chain μ.target.1
  obtain ⟨Sp, hfl, hSp⟩ := exists_flipTransformPrimeDivisor_isLabelCentre Q.chain μ.1.1 μ.1.2 hm
  obtain rfl : Sp = Pp := isLabelCentre_unique Q.chain hSp hp
  refine ⟨⟨finite_setOf_closure_subset (Q.chain.modelStructure μ.source.1)
      (topologicalKrullDim_model _ _) μ.badLocusSource.isClosed hcohm,
    badBranchCount_eq_finsum_branchNumber_of_dim (Q.chain.modelStructure μ.source.1)
      (topologicalKrullDim_model _ _) _ _⟩,
    hfl, finite_setOf_closure_subset (Q.chain.modelStructure μ.target.1)
      (topologicalKrullDim_model _ _) μ.badLocusTarget.isClosed hcohp,
    badBranchCount_eq_finsum_branchNumber_of_dim (Q.chain.modelStructure μ.target.1)
      (topologicalKrullDim_model _ _) _ _⟩

end MMP.Fourfold.StabilizedTail.PreparedChain
