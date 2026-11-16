module

public import MMP.Attr
public import MMP.AlgebraicGeometry.Singularities.LogDiscrepancy
public import MMP.AlgebraicGeometry.Singularities.Basic
import MMP.AlgebraicGeometry.Singularities.DltDiscrepancy
import MMP.AlgebraicGeometry.Singularities.PltFloorNormal
import MMP.AlgebraicGeometry.Singularities.DltFloorComponentsNormal
import MMP.AlgebraicGeometry.Singularities.DltAmplePerturbation
import MMP.AlgebraicGeometry.Morphisms.FiniteCoverTrace
import MMP.AlgebraicGeometry.Singularities.DiscrepancyLocal
import MMP.AlgebraicGeometry.Singularities.SncDiscrepancy
import MMP.AlgebraicGeometry.MMP.Flip.LogFlipSequenceQFactorial
import MMP.AlgebraicGeometry.Singularities.LogDiscrepancyComparison
import MMP.AlgebraicGeometry.MMP.Threefold.Canonical
import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso
import MMP.AlgebraicGeometry.Resolution.BirationalTransformTriple
import MMP.AlgebraicGeometry.MMP.Flip.DltPreservedKltPerturbation
import StacksFrontier.AlgebraicGeometry.Chow.DenominatorQuotients.ComponentOrder
import StacksFrontier.AlgebraicGeometry.Chow.PointClosureHeightOneCorrespondence
import MMP.AlgebraicGeometry.Resolution.MonomialIdealSNC
import MMP.AlgebraicGeometry.Singularities.Deminormal.Basic
import MMP.AlgebraicGeometry.Singularities.LogResolution.ReducedUnion

/-!
# The strata of a dlt pair meet the snc locus

Let `(Y, B)` be a dlt pair (Kollár–Mori 2.37) over an algebraically closed field of
characteristic zero, and `Z ⊆ Y` a closed set such that every divisor over `Y` with centre in `Z`
has positive log discrepancy (for instance the bad set of the pair, outside which `Y` is smooth
and `B` has snc support). For two distinct prime divisors `P ≠ Q` with coefficient at least one
in `B`, every irreducible component of `P ∩ Q` has its generic point outside `Z`. Hence every
irreducible subset `W ⊆ P ∩ Q` lies in an irreducible closed subset `closure {c} ⊆ P ∩ Q` with
`c ∉ Z` (Kollár–Mori 5.50–5.52 for the floor).

The proof takes an irreducible component `C` of `P ∩ Q` containing `W`, with generic point `c`,
and supposes `c ∈ Z`. On an affine neighbourhood `V` of `c`, perturbing the boundary as in the
proof of Kollár–Mori 5.52 gives an effective dlt boundary `Θ` on `V` with `⌊Θ⌋ = P + Q`. Every
generization of `c` lying on both `P` and `Q` is `c` itself, since `C` is a component. Let `U` be
the dlt witness of `(V, Θ)`.

* If `c ∉ U`, no point of `U` specializing to `c` lies on both `P` and `Q`, so `(V, Θ)` is plt
  near `c` (`MMP.Mori.IsDltPair.isAt_isPltPair_of_forall_specializes`). Its round down is then
  normal near `c` (Kollár–Mori 5.51), so `P` and `Q` are disjoint there, although both contain
  `c`.
* If `c ∈ U`, then `P` and `Q` are cut out at `c` by two members of a regular system of
  parameters of `𝒪_{Y,c}`. The maximal ideal is minimal over them, so `C` has codimension two by
  Krull's height theorem, and the blow-up of `C` gives a divisor with centre `C ⊆ Z` and
  discrepancy `1 - mult_C B ≤ -1` (Kollár–Mori 2.29), against the positivity over `Z`.

## Main results

* `MMP.Fourfold.exists_notMem_closure_of_isDltPair`: every irreducible subset of `P ∩ Q` lies in
  the closure of a point of `P ∩ Q` outside `Z`.

## Implementation notes

The irreducible component of `P ∩ Q` is found as a maximal preirreducible subset of the subspace
`P ∩ Q` (`exists_preirreducible`), whose image in `Y` is closed and maximal among irreducible
subsets of `P ∩ Q`. The argument runs with Kollár–Mori discrepancies (`MMP.Mori.IsDltPair`),
reached from `MMP.Intersection.IsDltPair` through `MMP.Threefold.Bridges.isDltPair_iff_isDltPair`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], 2.29, 2.37,
  5.50–5.52
* [J. Kollár, *Singularities of the minimal model program*][Kollar2013], 4.16
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

open MMP.Mori

/-- The preimage in a subspace `S` of a preirreducible subset of `S` is preirreducible. -/
private theorem isPreirreducible_preimage_subtypeVal {Y : Type*} [TopologicalSpace Y]
    {S W : Set Y} (hW : IsPreirreducible W) (hWS : W ⊆ S) :
    IsPreirreducible (Subtype.val ⁻¹' W : Set S) := by
  rintro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
  obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
  obtain ⟨y, hyW, hyu, hyv⟩ := hW u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
  exact ⟨⟨y, hWS hyW⟩, hyW, hyu, hyv⟩

/-- An irreducible subset `W` of a closed set `S` lies in a closed irreducible `C ⊆ S` maximal
among the irreducible subsets of `S`. -/
private theorem exists_isClosed_isIrreducible_maximal {Y : Type*} [TopologicalSpace Y]
    {S W : Set Y} (hS : IsClosed S) (hW : IsIrreducible W) (hWS : W ⊆ S) :
    ∃ C : Set Y, IsClosed C ∧ IsIrreducible C ∧ W ⊆ C ∧ C ⊆ S ∧
      ∀ C' : Set Y, IsIrreducible C' → C ⊆ C' → C' ⊆ S → C' = C := by
  obtain ⟨t, ht, hWt, hmax⟩ := exists_preirreducible (Subtype.val ⁻¹' W : Set S)
    (isPreirreducible_preimage_subtypeVal hW.isPreirreducible hWS)
  obtain ⟨w, hw⟩ := hW.nonempty
  have hti : IsIrreducible (Subtype.val '' t) :=
    ⟨⟨w, ⟨w, hWS hw⟩, hWt hw, rfl⟩, ht.image _ continuous_subtype_val.continuousOn⟩
  have hWC : W ⊆ Subtype.val '' t := fun y hy => ⟨⟨y, hWS hy⟩, hWt hy, rfl⟩
  have hCS : Subtype.val '' t ⊆ S := by rintro _ ⟨y, -, rfl⟩; exact y.2
  -- maximality, before closedness
  have hmaxC : ∀ C' : Set Y, IsPreirreducible C' → Subtype.val '' t ⊆ C' → C' ⊆ S →
      C' = Subtype.val '' t := by
    intro C' hC' htC' hC'S
    have heq := hmax _ (isPreirreducible_preimage_subtypeVal hC' hC'S)
      fun y hy => htC' ⟨y, hy, rfl⟩
    refine (Set.Subset.antisymm ?_ htC')
    intro y hy
    have : (⟨y, hC'S hy⟩ : S) ∈ t := by rw [← heq]; exact hy
    exact ⟨_, this, rfl⟩
  have hclosed : IsClosed (Subtype.val '' t) := by
    have h := hmaxC (closure (Subtype.val '' t)) hti.isPreirreducible.closure subset_closure
      (closure_minimal hCS hS)
    rw [← h]; exact isClosed_closure
  exact ⟨_, hclosed, hti, hWC, hCS, fun C' hC' h1 h2 => hmaxC C' hC'.isPreirreducible h1 h2⟩

/-! ### The two cases at the generic point of a component of `P ∩ Q` -/

section Cases

variable {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
  [IsNormal X] {sX : X ⟶ Spec (.of k)} {n : ℕ} {K : Divisor X}

/-- On an affine scheme the zero divisor is ample. -/
private theorem isAmple_zero_of_isAffine {Y : Scheme.{0}} [IsAffine Y] [IsIntegral Y]
    [IsLocallyNoetherian Y] [IsNormal Y] :
    Divisor.IsAmple (0 : Divisor Y) Divisor.isCartier_zero := by
  have := (Divisor.isCartier_zero (X := Y)).isInvertibleModule_divisorialSheaf
  exact (Stacks.RelativeAmple.isQuasiAffine_iff_isAmple_of_iso_unitModule Y _
    Divisor.divisorialSheafZeroIso).mp inferInstance

/-- **Isolating two components of the round down.** On an affine dlt pair `(X, Δ)` of dimension
`n ≥ 2`, two distinct prime divisors `P ≠ Q` with coefficient `1` in `Δ` are the round down of an
effective dlt boundary `Θ = Δ - εΔ₁ + εD`, with `Δ₁ = Δ - P - Q` and `D` the perturbation of `Δ₁`
along the ample divisor `0` with no component in common with `Δ`. -/
private theorem exists_isDltPair_roundDown_eq_add [IsAffine X] [IsAlgClosed k] [CharZero k]
    {Δ : QDivisor X} (h : IsDltPair sX n K Δ) (hn : 2 ≤ n) {P Q : MMP.Mori.PrimeDivisor X}
    (hPQ : P ≠ Q) (hP : Δ.coeff P = 1) (hQ : Δ.coeff Q = 1) :
    ∃ Θ : QDivisor X, 0 ≤ Θ ∧ IsDltPair sX n K Θ ∧
      Θ.roundDown = Finsupp.single P 1 + Finsupp.single Q 1 := by
  have : LocallyOfFiniteType sX := h.1.1.1.toLocallyOfFiniteType
  set Δ₁ : QDivisor X := Δ - Finsupp.single P 1 - Finsupp.single Q 1 with hΔ₁
  have hΔ₁P : Δ₁.coeff P = 0 := by
    rw [hΔ₁, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub, hP,
      DivisorWithCoeffs.coeff_single_self, DivisorWithCoeffs.coeff_single_of_ne hPQ.symm]
    norm_num
  have hΔ₁Q : Δ₁.coeff Q = 0 := by
    rw [hΔ₁, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub, hQ,
      DivisorWithCoeffs.coeff_single_self, DivisorWithCoeffs.coeff_single_of_ne hPQ]
    norm_num
  have hΔ₁W : ∀ W, W ≠ P → W ≠ Q → Δ₁.coeff W = Δ.coeff W := fun W hWP hWQ => by
    rw [hΔ₁, DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_sub,
      DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hWP),
      DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hWQ), sub_zero, sub_zero]
  obtain ⟨c, -, D, hDeff, hDΔ, -, ε₀, hε₀, hε⟩ :=
    h.exists_forall_isDltPair_sub_smul_add_smul_of_disjoint
      (MMP.Mori.isQuasiProjective_of_isAffine _) hn
      Divisor.isCartier_zero isAmple_zero_of_isAffine
      (fun W => by
        by_cases hWP : W = P
        · rw [hWP, hΔ₁P]
        · by_cases hWQ : W = Q
          · rw [hWQ, hΔ₁Q]
          · rw [hΔ₁W W hWP hWQ]; exact (h.2.1 W).1)
      (fun W => by
        rw [hΔ₁, sub_sub, sub_sub_cancel]
        exact add_nonneg (Finsupp.single_nonneg.mpr zero_le_one W)
          (Finsupp.single_nonneg.mpr zero_le_one W))
  have hD0 : ∀ W, Δ.coeff W ≠ 0 → D.coeff W = 0 := fun W hW => by
    by_contra hne
    exact Finset.disjoint_left.mp hDΔ (Finsupp.mem_support_iff.mpr hne)
      (Finsupp.mem_support_iff.mpr hW)
  have hd₁ := hε (ε₀ / 2) (by positivity) (by linarith)
  have hd := hε (ε₀ / 4) (by positivity) (by linarith)
  refine ⟨_, fun W => (hd.2.1 W).1, hd, DivisorWithCoeffs.ext' fun W => ?_⟩
  have hb₁ := (hd₁.2.1 W).2
  have hb := (hd.2.1 W).1
  have ha := h.2.1 W
  have hDW := hDeff W
  simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_add,
    DivisorWithCoeffs.coeff_sub, DivisorWithCoeffs.coeff_smul, smul_eq_mul] at hb₁ hb ⊢
  by_cases hWP : W = P
  · subst hWP
    rw [hD0 W (by rw [hP]; norm_num), hP, hΔ₁P, DivisorWithCoeffs.coeff_single_self,
      DivisorWithCoeffs.coeff_single_of_ne hPQ.symm]
    norm_num
  · by_cases hWQ : W = Q
    · subst hWQ
      rw [hD0 W (by rw [hQ]; norm_num), hQ, hΔ₁Q, DivisorWithCoeffs.coeff_single_self,
        DivisorWithCoeffs.coeff_single_of_ne hPQ]
      norm_num
    · rw [hΔ₁W W hWP hWQ] at hb₁ hb ⊢
      rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hWP),
        DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hWQ), add_zero, Int.floor_eq_zero_iff]
      by_cases hΔW : Δ.coeff W = 0
      · rw [hΔW] at hb₁ hb ⊢
        constructor <;> nlinarith
      · rw [hD0 W hΔW] at hb ⊢
        exact ⟨hb, by nlinarith [ha.2, lt_of_le_of_ne ha.1 (Ne.symm hΔW)]⟩

/-- **The plt case.** Let `(X, Θ)` be an effective dlt pair of dimension `n ≥ 2` whose round down
is `P + Q` with `P ≠ Q`, with dlt witness `U`, and `x ∈ P ∩ Q` such that no point of `U`
specializing to `x` lies on both `P` and `Q`. This is impossible: `(X, Θ)` would be plt near `x`,
so `⌊Θ⌋` would be normal near `x` and `P`, `Q` disjoint there. -/
private theorem false_of_isDltPair_roundDown_eq_add [IsAlgClosed k] [CharZero k]
    {Θ : QDivisor X} (h : IsDltPair sX n K Θ) (hn : 2 ≤ n) (hΘ : 0 ≤ Θ)
    {P Q : MMP.Mori.PrimeDivisor X} (hPQ : P ≠ Q)
    (hfloor : Θ.roundDown = Finsupp.single P 1 + Finsupp.single Q 1)
    {U : X.Opens} (hUsm : U ≤ smoothLocus sX) (hsnc : (Θ.restrictOpen U).IsSNC (U.ι ≫ sX))
    (hZ : ∀ (D : DivisorOver k sX) (a : ℚ), (D.center : Set X) ⊆ (U : Set X)ᶜ →
      IsDiscrepancy sX n K Θ D a → -1 < a)
    {x : X} (hxP : x ∈ P.support) (hxQ : x ∈ Q.support)
    (hx : ∀ y ∈ U, y ⤳ x → y ∈ P.support → y ∈ Q.support → False) : False := by
  classical
  have hPQor : ∀ R, Θ.roundDown.coeff R ≠ 0 → R = P ∨ R = Q := by
    intro R hR
    by_contra hne
    push Not at hne
    apply hR
    rw [hfloor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_single_of_ne hne.1.symm,
      DivisorWithCoeffs.coeff_single_of_ne hne.2.symm, add_zero]
  have hx' : ∀ y ∈ U, y ⤳ x →
      {R : MMP.Mori.PrimeDivisor X | Θ.roundDown.coeff R ≠ 0 ∧ y ∈ R.support}.Subsingleton := by
    intro y hyU hyx R₁ hR₁ R₂ hR₂
    rcases hPQor R₁ hR₁.1 with rfl | rfl <;> rcases hPQor R₂ hR₂.1 with rfl | rfl
    · rfl
    · exact (hx y hyU hyx hR₁.2 hR₂.2).elim
    · exact (hx y hyU hyx hR₂.2 hR₁.2).elim
    · rfl
  obtain ⟨V', hxV', hne, hplt⟩ := h.isAt_isPltPair_of_forall_specializes hn hUsm hsnc hZ hx'
  have hdlt := h.restrictOpen V'
  have hΘ' : 0 ≤ Θ.restrictOpen V' := fun W => hΘ _
  have hnorm := hdlt.isNormal_suppScheme_roundDown hplt hn hΘ'
  have hcoeff : ∀ W : MMP.Mori.PrimeDivisor V',
      (Θ.restrictOpen V').roundDown.coeff W =
        Θ.roundDown.coeff (OpenWeilRestriction.primeDivisorMap V'.ι W) := fun W => by
    simp only [DivisorWithCoeffs.coeff_roundDown, DivisorWithCoeffs.coeff_restrictOpen]
  have hred : MMP.Intersection.IsReducedEffective (Θ.restrictOpen V').roundDown := fun W => by
    rw [hcoeff, hfloor, DivisorWithCoeffs.coeff_add]
    by_cases hWP : OpenWeilRestriction.primeDivisorMap V'.ι W = P
    · rw [hWP, DivisorWithCoeffs.coeff_single_self, DivisorWithCoeffs.coeff_single_of_ne hPQ.symm]
      right; rfl
    · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hWP)]
      by_cases hWQ : OpenWeilRestriction.primeDivisorMap V'.ι W = Q
      · rw [hWQ, DivisorWithCoeffs.coeff_single_self]; right; rfl
      · rw [DivisorWithCoeffs.coeff_single_of_ne (Ne.symm hWQ)]; left; rfl
  have hdisj := MMP.Mori.DivisorWithCoeffs.pairwise_disjoint_support_of_isNormal_suppScheme
    (V'.ι ≫ sX) hdlt.1.1 _ hred
  let xV : V' := ⟨x, hxV' rfl⟩
  obtain ⟨P', hP'⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V'.ι P xV hxP
  obtain ⟨Q', hQ'⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V'.ι Q xV hxQ
  have hP'm : P' ∈ (Θ.restrictOpen V').roundDown.support := by
    rw [Finsupp.mem_support_iff]
    change (Θ.restrictOpen V').roundDown.coeff P' ≠ 0
    rw [hcoeff, hP', hfloor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_single_self,
      DivisorWithCoeffs.coeff_single_of_ne hPQ.symm]
    norm_num
  have hQ'm : Q' ∈ (Θ.restrictOpen V').roundDown.support := by
    rw [Finsupp.mem_support_iff]
    change (Θ.restrictOpen V').roundDown.coeff Q' ≠ 0
    rw [hcoeff, hQ', hfloor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_single_self,
      DivisorWithCoeffs.coeff_single_of_ne hPQ]
    norm_num
  have hne' : P' ≠ Q' := fun h' => hPQ (by rw [← hP', ← hQ', h'])
  exact Set.disjoint_left.mp (hdisj hP'm hQ'm hne')
    ((MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff V'.ι P' xV).mp
      (hP' ▸ hxP))
    ((MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff V'.ι Q' xV).mp
      (hQ' ▸ hxQ))

/-- In a Noetherian local ring, a nonzero element `g` of the maximal ideal has a finite order
`sup {s | g ∈ 𝔪^s}`, which is at least one. -/
private theorem one_le_toNat_iSup_mem_pow {R : Type*} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] {g : R} (hg : g ∈ IsLocalRing.maximalIdeal R) (hg0 : g ≠ 0) :
    1 ≤ (⨆ (s : ℕ) (_ : g ∈ IsLocalRing.maximalIdeal R ^ s), (s : ℕ∞)).toNat := by
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℕ, g ∉ IsLocalRing.maximalIdeal R ^ s₀ := by
    by_contra hall
    push Not at hall
    have : g ∈ ⨅ i, IsLocalRing.maximalIdeal R ^ i := Ideal.mem_iInf.mpr hall
    rw [hK, Ideal.mem_bot] at this
    exact hg0 this
  have hle : (⨆ (s : ℕ) (_ : g ∈ IsLocalRing.maximalIdeal R ^ s), (s : ℕ∞)) ≤ s₀ := by
    refine iSup₂_le fun s hs => ?_
    by_contra hlt
    push Not at hlt
    exact hs₀ (Ideal.pow_le_pow_right (by exact_mod_cast hlt.le) hs)
  have h1 : (1 : ℕ∞) ≤ ⨆ (s : ℕ) (_ : g ∈ IsLocalRing.maximalIdeal R ^ s), (s : ℕ∞) :=
    le_iSup₂_of_le (f := fun (s : ℕ) (_ : g ∈ IsLocalRing.maximalIdeal R ^ s) => (s : ℕ∞)) 1
      (by simpa using hg) (by norm_num)
  obtain ⟨N, hN⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top s₀) hle)
  rw [← hN] at h1 ⊢
  simpa using h1

/-- **The snc case: blowing up a codimension-two stratum.** Let `(X, B)` be a pair with `B ≥ 0`,
`P ≠ Q` prime divisors with coefficient at least one, and `x ∈ P ∩ Q` such that every
generization of `x` on both `P` and `Q` is `x` itself. If `P` and `Q` are cut out at `x` by two
members `z_i, z_j` of a regular system of parameters of `𝒪_{X,x}`, then the blow-up of
`closure {x}` gives a divisor over `X` with centre `closure {x}` and discrepancy at most `-1`. -/
private theorem exists_isDiscrepancy_le_neg_one_of_isRegularSystemOfParameters [IsAlgClosed k]
    [CharZero k] {B : QDivisor X} (hpair : IsPairWith sX n K B) (hB : ∀ Γ, 0 ≤ B.coeff Γ)
    {P Q : MMP.Mori.PrimeDivisor X} (hPQ : P ≠ Q) (hP : 1 ≤ B.coeff P) (hQ : 1 ≤ B.coeff Q)
    {x : X} (hxP : x ∈ P.support) (hxQ : x ∈ Q.support)
    (hx : ∀ y : X, y ⤳ x → y ∈ P.support → y ∈ Q.support → y = x)
    {m : ℕ} {z : Fin m → X.presheaf.stalk x} (hz : IsRegularSystemOfParameters z) {i j : Fin m}
    (hij : i ≠ j) (hPi : IdealSheafData.stalk P.idealSheaf x = Ideal.span {z i})
    (hQj : IdealSheafData.stalk Q.idealSheaf x = Ideal.span {z j}) :
    ∃ D : DivisorOver k sX, D.f D.E.genericPoint = x ∧ ∃ a : ℚ,
      IsDiscrepancy sX n K B D a ∧ a ≤ -1 := by
  classical
  have hX := hpair.1
  -- replace `x` by the generic point of `W = closure {x}`
  obtain ⟨W, hWx⟩ : ∃ W : IrreducibleCloseds X, W.isIrreducible.genericPoint = x :=
    ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩,
      (IsIrreducible.isGenericPoint_genericPoint_closure _).eq (by
        change closure {x} = closure (closure {x})
        rw [closure_closure])⟩
  subst hWx
  have hreg : IsRegularLocalRing (X.presheaf.stalk W.isIrreducible.genericPoint) :=
    MMP.Mori.isRegularLocalRing_of_isRegularSystemOfParameters hz
  have hzm : ∀ l, z l ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint) :=
    fun l => by rw [← hz.1]; exact Ideal.subset_span ⟨l, rfl⟩
  -- `𝔪` is minimal over `(z_i, z_j)`
  have hmin : IsLocalRing.maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint) ∈
      (Ideal.span {z i, z j}).minimalPrimes := by
    refine ⟨⟨inferInstance, ?_⟩, fun p ⟨hp, hIp⟩ hpm => ?_⟩
    · rw [Ideal.span_le]
      rintro _ (rfl | rfl)
      · exact hzm i
      · exact hzm j
    · let q : PrimeSpectrum (X.presheaf.stalk W.isIrreducible.genericPoint) := ⟨p, hp⟩
      have hzi : z i ∈ p := hIp (Ideal.subset_span (Set.mem_insert _ _))
      have hzj : z j ∈ p := hIp (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
      have hyP : X.fromSpecStalk W.isIrreducible.genericPoint q ∈ P.support :=
        (MMP.Resolution.fromSpecStalk_mem_support_iff_stalk_le P.idealSheaf _ q).mpr (by
          rw [hPi, Ideal.span_le, Set.singleton_subset_iff]; exact hzi)
      have hyQ : X.fromSpecStalk W.isIrreducible.genericPoint q ∈ Q.support :=
        (MMP.Resolution.fromSpecStalk_mem_support_iff_stalk_le Q.idealSheaf _ q).mpr (by
          rw [hQj, Ideal.span_le, Set.singleton_subset_iff]; exact hzj)
      have heq := hx _ (MMP.Resolution.specializes_fromSpecStalk _ q) hyP hyQ
      have heq' :=
        heq.trans (Scheme.fromSpecStalk_closedPoint (x := W.isIrreducible.genericPoint)).symm
      have hq : q = IsLocalRing.closedPoint _ :=
        (X.fromSpecStalk W.isIrreducible.genericPoint).isEmbedding.injective heq'
      have : p = IsLocalRing.maximalIdeal _ := congrArg PrimeSpectrum.asIdeal hq
      exact this ▸ le_rfl
  -- hence `dim 𝒪_{X,η_W} = 2`
  have hm2 : 2 ≤ m := by
    rcases Nat.lt_or_ge m 2 with h | h
    · interval_cases m <;> exact absurd (Subsingleton.elim i j) hij
    · exact h
  have hht : (IsLocalRing.maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint)).height
      ≤ 2 := by
    refine (Ideal.height_le_spanRank_toENat_of_mem_minimalPrimes _ _ hmin).trans ?_
    have h1 := Submodule.spanRank_span_le_card (R := X.presheaf.stalk W.isIrreducible.genericPoint)
      ({z i, z j} : Set _)
    have h2 : Cardinal.mk ({z i, z j} : Set (X.presheaf.stalk W.isIrreducible.genericPoint)) ≤ 2 :=
      calc _ ≤ Cardinal.mk ({z j} : Set (X.presheaf.stalk W.isIrreducible.genericPoint)) + 1 :=
            Cardinal.mk_insert_le
        _ = 2 := by rw [Cardinal.mk_singleton]; norm_num
    have := Cardinal.toENat.monotone' (h1.trans h2)
    simpa using this
  have hm : m = 2 := by
    have h5 := WithBot.coe_le_coe.mpr hht
    rw [IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hz.2] at h5
    have : m ≤ 2 := by exact_mod_cast h5
    omega
  have hco : Order.coheight W.isIrreducible.genericPoint =
      (IsLocalRing.maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint)).height := by
    have h := Stacks.Chow.coheight_fromSpecStalk_eq_height (W := X) W.isIrreducible.genericPoint
      (IsLocalRing.closedPoint (X.presheaf.stalk W.isIrreducible.genericPoint))
    rw [Scheme.fromSpecStalk_closedPoint] at h
    exact h
  have hcodim : ((2 : ℕ) : ℕ∞) = codimension W := by
    rw [MMP.Flips.codimension_eq_coheight_genericPoint, hco]
    have := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
      (R := X.presheaf.stalk W.isIrreducible.genericPoint)
    rw [hz.2, hm] at this
    have h7 : ((IsLocalRing.maximalIdeal (X.presheaf.stalk W.isIrreducible.genericPoint)).height :
        WithBot ℕ∞) = ((2 : ℕ∞) : WithBot ℕ∞) := by rw [this]; rfl
    rw [WithBot.coe_inj] at h7
    rw [h7]; rfl
  -- the blow-up divisor
  obtain ⟨⟨D, j', hj', hjf, hE⟩, -⟩ :=
    MMP.Flips.valuation_eq_blowupDivisor_of_isOpenImmersion_blowUp sX hX W (hcodim ▸ by norm_num)
      hreg
  have hdisc := MMP.Mori.isDiscrepancy_blowUp_of_isRegularLocalRing sX hX hpair.2.1 B hpair.2.2 W
    hcodim le_rfl hreg D j' hjf hE
  refine ⟨D, hE, _, hdisc, ?_⟩
  -- the multiplicities of `P` and `Q` along `W` are at least one
  have hmult : ∀ (Γ : MMP.Mori.PrimeDivisor X) (l : Fin m),
      IdealSheafData.stalk Γ.idealSheaf W.isIrreducible.genericPoint = Ideal.span {z l} →
        1 ≤ (Γ.multiplicityAlong W).toNat := by
    intro Γ l hΓ
    rw [Γ.multiplicityAlong_eq_of_stalkIdeal_eq_span W
      (by rw [Scheme.IdealSheafData.stalkIdeal_eq_stalk]; exact hΓ)]
    exact one_le_toNat_iSup_mem_pow (hzm l)
      (MMP.Resolution.ne_zero_of_isRegularSystemOfParameters hz l)
  have hPm := hmult P i hPi
  have hQm := hmult Q j hQj
  have hsum : (2 : ℚ) ≤ B.sum fun Γ b => b * ((Γ.multiplicityAlong W).toNat : ℚ) := by
    have hPs : P ∈ B.support := Finsupp.mem_support_iff.mpr (by
      intro h0; change B.coeff P = 0 at h0; rw [h0] at hP; norm_num at hP)
    have hQs : Q ∈ B.support := Finsupp.mem_support_iff.mpr (by
      intro h0; change B.coeff Q = 0 at h0; rw [h0] at hQ; norm_num at hQ)
    have hsub : ({P, Q} : Finset (MMP.Mori.PrimeDivisor X)) ⊆ B.support := by
      intro R hR
      rcases Finset.mem_insert.mp hR with rfl | hR
      · exact hPs
      · rw [Finset.mem_singleton.mp hR]; exact hQs
    have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun Γ => B Γ * ((Γ.multiplicityAlong W).toNat : ℚ))
      (fun Γ _ _ => mul_nonneg (hB Γ) (by positivity))
    rw [Finset.sum_pair hPQ] at hle
    have h1 : (1 : ℚ) ≤ ((P.multiplicityAlong W).toNat : ℚ) := by exact_mod_cast hPm
    have h2 : (1 : ℚ) ≤ ((Q.multiplicityAlong W).toNat : ℚ) := by exact_mod_cast hQm
    have hP' : (1 : ℚ) ≤ B P := hP
    have hQ' : (1 : ℚ) ≤ B Q := hQ
    refine le_trans ?_ hle
    nlinarith
  push_cast
  linarith

end Cases

/-- **The generic point of a component of `P ∩ Q` lies outside the bad set.** For a dlt pair
`(Y, B)`, a closed `Z` over which every divisor has positive log discrepancy, and distinct prime
divisors `P ≠ Q` of coefficient at least one, the generic point of every closed irreducible
`C ⊆ P ∩ Q` maximal among the irreducible subsets of `P ∩ Q` lies outside `Z`. -/
private theorem genericPoint_notMem_of_isDltPair {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {BY : QDivisor Y} (hB : MMP.Intersection.IsDltPair sY BY) {Z : Closeds Y}
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sY), (D.center : Set Y) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sY n (MMP.Mori.QDivisor.toRDivisor BY) D a →
        0 < a)
    {P Q : MMP.Mori.PrimeDivisor Y} (hPQ : P ≠ Q) (hP : 1 ≤ BY.coeff P) (hQ : 1 ≤ BY.coeff Q)
    (hS : IsClosed ((P.support : Set Y) ∩ Q.support))
    {C : Set Y} (hCc : IsClosed C) (hCi : IsIrreducible C)
    (hCPQ : C ⊆ (P.support : Set Y) ∩ Q.support)
    (hCmax : ∀ C' : Set Y, IsIrreducible C' → C ⊆ C' → C' ⊆ (P.support : Set Y) ∩ Q.support →
      C' = C) :
    hCi.genericPoint ∉ (Z : Set Y) := by
  intro hcZ
  obtain ⟨⟨hpairI, -, -⟩, hle1, -⟩ := id hB
  obtain ⟨hX, n, K, hK, -⟩ := hpairI
  have hBm : MMP.Mori.IsDltPair sY n K BY :=
    (MMP.Threefold.Bridges.isDltPair_iff_isDltPair sY hK BY).mp hB
  have hPw : IsPairWith sY n K BY := hBm.1
  have hP1 : BY.coeff P = 1 := le_antisymm (hle1 P) hP
  have hQ1 : BY.coeff Q = 1 := le_antisymm (hle1 Q) hQ
  set c := hCi.genericPoint
  have hc : closure {c} = C := by
    rw [hCi.isGenericPoint_genericPoint_closure.def, hCc.closure_eq]
  have hcPQ : c ∈ (P.support : Set Y) ∩ Q.support := hCPQ (hc ▸ subset_closure rfl)
  -- a generization of `c` on `P ∩ Q` is `c`
  have hmax : ∀ y : Y, y ⤳ c → y ∈ P.support → y ∈ Q.support → y = c := by
    intro y hyc hyP hyQ
    have h1 : closure {y} = C := hCmax _ isIrreducible_singleton.closure
      (hc ▸ closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyc))
        isClosed_closure)
      (closure_minimal (Set.singleton_subset_iff.mpr ⟨hyP, hyQ⟩) hS)
    have hcy : c ⤳ y := specializes_iff_mem_closure.mpr (by rw [hc, ← h1]; exact subset_closure rfl)
    exact (hyc.antisymm hcy).eq
  -- the dimension is at least two
  have hn : 2 ≤ n := by
    have hcne : c ≠ P.genericPoint := fun h => hPQ
      (MMP.Intersection.primeDivisor_eq_of_genericPoint_mem_support (h ▸ hcPQ.2)).symm
    have hηc : P.genericPoint ⤳ c := by
      rw [specializes_iff_mem_closure, ← P.support_eq_closure]; exact hcPQ.1
    have hlt : c < P.genericPoint :=
      lt_of_le_not_ge hηc fun hcη => hcne (Specializes.antisymm hcη hηc).eq
    have h2 := Order.coheight_add_one_le hlt
    rw [P.coheight_genericPoint] at h2
    have h3 : (Order.coheight c : WithBot ℕ∞) ≤ topologicalKrullDim Y := by
      rw [topologicalKrullDim,
        Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := (Y : Type)))]
      exact Order.coheight_le_krullDim c
    rw [hK.topologicalKrullDim_eq] at h3
    have h4 : ((2 : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) :=
      (WithBot.coe_le_coe.mpr (by exact_mod_cast h2)).trans h3
    exact_mod_cast WithBot.coe_le_coe.mp h4
  -- an affine neighbourhood of `c`
  obtain ⟨V, hVa, hcV, -⟩ := exists_isAffineOpen_mem_and_subset (x := c) (U := ⊤) trivial
  have : Nonempty V := ⟨⟨c, hcV⟩⟩
  have : IsAffine V := hVa
  set cV : V := ⟨c, hcV⟩
  obtain ⟨PV, hPV⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V.ι P cV hcPQ.1
  obtain ⟨QV, hQV⟩ := MMP.Threefold.Mori.OpenRestriction.exists_primeDivisorMap_eq_of_mem_support
    V.ι Q cV hcPQ.2
  have hPQV : PV ≠ QV := fun h => hPQ (by rw [← hPV, ← hQV, h])
  have memP : ∀ y : V, y ∈ PV.support ↔ V.ι y ∈ P.support := fun y => by
    rw [← hPV]
    exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff V.ι PV y).symm
  have memQ : ∀ y : V, y ∈ QV.support ↔ V.ι y ∈ Q.support := fun y => by
    rw [← hQV]
    exact (MMP.Threefold.Mori.OpenRestriction.mem_support_primeDivisorMap_iff V.ι QV y).symm
  have hcVP : cV ∈ PV.support := (memP cV).2 hcPQ.1
  have hcVQ : cV ∈ QV.support := (memQ cV).2 hcPQ.2
  have hmaxV : ∀ y : V, y ⤳ cV → y ∈ PV.support → y ∈ QV.support → y = cV := by
    intro y hy hyP hyQ
    exact V.ι.isOpenEmbedding.injective
      (hmax (V.ι y) (hy.map V.ι.continuous) ((memP y).1 hyP) ((memQ y).1 hyQ))
  have hBV := hBm.restrictOpen V
  have hPV1 : (BY.restrictOpen V).coeff PV = 1 := by
    rw [DivisorWithCoeffs.coeff_restrictOpen, hPV, hP1]
  have hQV1 : (BY.restrictOpen V).coeff QV = 1 := by
    rw [DivisorWithCoeffs.coeff_restrictOpen, hQV, hQ1]
  obtain ⟨Θ, hΘ0, hΘ, hfloor⟩ := exists_isDltPair_roundDown_eq_add hBV hn hPQV hPV1 hQV1
  obtain ⟨U, -, hUsm, hUsnc, hUZ, -⟩ := MMP.Threefold.Mori.IsDltPair.exists_open_nonempty hΘ
  by_cases hcU : cV ∈ U
  · -- the snc case: blow up `closure {c}`
    obtain ⟨m, z, jj, hz, hjj, hI⟩ :=
      (MMP.Threefold.Mori.OpenRestriction.sncStalk_restrict_iff U.ι Θ ⟨cV, hcU⟩).mp
        (hUsnc.2 ⟨cV, hcU⟩)
    have hmemΘ : ∀ R : MMP.Mori.PrimeDivisor V, Θ.roundDown.coeff R = 1 → R ∈ Θ.support := by
      intro R hR
      rw [DivisorWithCoeffs.coeff_roundDown, Int.floor_eq_iff] at hR
      refine Finsupp.mem_support_iff.mpr fun h0 => ?_
      have : (1 : ℚ) ≤ Θ.coeff R := by exact_mod_cast hR.1
      rw [DivisorWithCoeffs.coeff, h0] at this
      norm_num at this
    have hfP : Θ.roundDown.coeff PV = 1 := by
      rw [hfloor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_single_self,
        DivisorWithCoeffs.coeff_single_of_ne hPQV.symm, add_zero]
    have hfQ : Θ.roundDown.coeff QV = 1 := by
      rw [hfloor, DivisorWithCoeffs.coeff_add, DivisorWithCoeffs.coeff_single_self,
        DivisorWithCoeffs.coeff_single_of_ne hPQV, zero_add]
    let eP : {E : MMP.Mori.PrimeDivisor V // E ∈ Θ.support ∧ U.ι ⟨cV, hcU⟩ ∈ E.support} :=
      ⟨PV, hmemΘ PV hfP, hcVP⟩
    let eQ : {E : MMP.Mori.PrimeDivisor V // E ∈ Θ.support ∧ U.ι ⟨cV, hcU⟩ ∈ E.support} :=
      ⟨QV, hmemΘ QV hfQ, hcVQ⟩
    have hij : jj eP ≠ jj eQ := fun h => hPQV (congrArg Subtype.val (hjj h))
    obtain ⟨D, hDc, a, ha, ha1⟩ :=
      exists_isDiscrepancy_le_neg_one_of_isRegularSystemOfParameters hBV.1
        (fun Γ => (hBV.2.1 Γ).1) hPQV hPV1.ge hQV1.ge hcVP hcVQ hmaxV hz hij (hI eP) (hI eQ)
    obtain ⟨D₁, hD₁, ha₁⟩ := MMP.Mori.exists_isDiscrepancy_of_restrictOpen hPw V ha
    have hcen : (D₁.center : Set Y) ⊆ Z := by
      rw [D₁.center_eq_closure_genericPoint, hD₁, hDc]
      exact closure_minimal (Set.singleton_subset_iff.mpr hcZ) Z.isClosed
    have : LocallyOfFiniteType sY := hPw.1.1.toLocallyOfFiniteType
    have : QuasiCompact sY := hPw.1.1.toQuasiCompact
    have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace sY
    have := MMP.Threefold.Bridges.neg_one_lt_of_forall_isLogDiscrepancy_pos hPw (hpos n) hcen ha₁
    linarith
  · -- the plt case
    exact false_of_isDltPair_roundDown_eq_add hΘ hn hΘ0 hPQV hfloor hUsm hUsnc hUZ hcVP hcVQ
      fun y hyU hy hyP hyQ => hcU (hmaxV y hy hyP hyQ ▸ hyU)

/-- **The strata of a dlt pair meet the snc locus** (Kollár–Mori 5.50 for floor components).
Let `(Y, B_Y)` be a dlt pair, `Z` a closed set such that every divisor over `Y` centred in `Z` has
positive log discrepancy, and `P ≠ Q` prime divisors of coefficient
at least one. Every irreducible subset of `P ∩ Q` lies in an irreducible closed subset of `P ∩ Q`
whose generic point lies outside `Z`. -/
theorem exists_notMem_closure_of_isDltPair {k : Type} [Field k] [IsAlgClosed k] [CharZero k]
    {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of k)} [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    {BY : QDivisor Y} (hB : MMP.Intersection.IsDltPair sY BY) {Z : Closeds Y}
    (hpos : ∀ (n : ℕ) (D : DivisorOver k sY), (D.center : Set Y) ⊆ Z →
      ∀ a : ℝ, MMP.Intersection.IsLogDiscrepancy sY n (MMP.Mori.QDivisor.toRDivisor BY) D a →
        0 < a)
    {P Q : MMP.Mori.PrimeDivisor Y} (hPQ : P ≠ Q) (hP : 1 ≤ BY.coeff P) (hQ : 1 ≤ BY.coeff Q)
    {W : Set Y} (hW : IsIrreducible W) (hWPQ : W ⊆ (P.support : Set Y) ∩ Q.support) :
    ∃ c : Y, c ∉ (Z : Set Y) ∧ W ⊆ closure {c} ∧
      closure {c} ⊆ (P.support : Set Y) ∩ Q.support := by
  have hS : IsClosed ((P.support : Set Y) ∩ Q.support) := by
    rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure,
      AlgebraicGeometry.PrimeDivisor.support_eq_closure]
    exact isClosed_closure.inter isClosed_closure
  obtain ⟨C, hCc, hCi, hWC, hCPQ, hCmax⟩ := exists_isClosed_isIrreducible_maximal hS hW hWPQ
  set c := hCi.genericPoint
  have hc : closure {c} = C := by
    rw [hCi.isGenericPoint_genericPoint_closure.def, hCc.closure_eq]
  exact ⟨c, genericPoint_notMem_of_isDltPair hB hpos hPQ hP hQ hS hCc hCi hCPQ hCmax,
    hc ▸ hWC, hc ▸ hCPQ⟩

end MMP.Fourfold
