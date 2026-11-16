module

public import MMP.AlgebraicGeometry.ProjectiveBundle.UniversalProperty
public import MMP.AlgebraicGeometry.Morphisms.Birational.ZariskiMainTheorem
public import MMP.AlgebraicGeometry.Singularities.SncLogDiscrepancyFormula

/-!
# Log discrepancies over an snc divisor; factorization through a contraction

This file holds two results.

**A lower bound for log discrepancies.** Let `Y` be a smooth variety, `S` an snc divisor on `Y`
and `B` an `ℝ`-divisor supported on `S`. Split the components of `S` into a finite set `𝓔` (the
components `E_j`, along which the coefficient `e_j` of `B` is `≤ 1`) and the rest (the components
`H_k`, along which `1 - h_k ≥ c` for a fixed `0 ≤ c ≤ 1`). If `ν` is a divisor over `Y` whose
center `Z` is contained in fewer members of `𝓔` than its codimension, then `a_ℓ(ν, Y, B) ≥ c`.
From the snc formula `a_ℓ(ν, Y, B) = l + ∑_P n_P (1 - b_P)` every term is nonnegative; if
`l ≥ 1` the bound is `1 ≥ c`, and if `l = 0` the codimension count produces a component
`P ∉ 𝓔` containing the center, whose term is `≥ 1 - b_P ≥ c`.

**The curve criterion for factorization.** Let `p : W ⟶ X` be a proper birational morphism of
varieties over a field `k` with `X` normal, and let `q : W ⟶ Y` be a morphism. If `q` maps to a
point every integral curve of `W` that `p` maps to a point, then `q` factors uniquely through
`p`. The argument only uses that `p` is proper with `𝒪_X ≅ p_* 𝒪_W`, which Zariski's main
theorem provides in the birational normal case.

Since `p_* 𝒪_W = 𝒪_X` and `p` is proper, the fibres of `p` are connected. For a fibre over a
closed point, constancy of `q` follows from connectedness: the fibre is the union of the
closures of finitely many of its points (it lies in the preimage of an affine open, a Noetherian
scheme), `q` is constant on each such closure because every point of it is joined to a closed
point by an integral curve inside the fibre, and two closed sets of the cover with different
`q`-values are disjoint. A general fibre is handled by specialising to closed points, `W` being
Jacobson. The rigidity factorization `MMP.existsUnique_comp_eq_of_isIso_c` then gives `h`.

## Main results

* `MMP.Flips.le_logDiscrepancy_of_isSNCDivisor`: the bound `c ≤ a_ℓ(ν, Y, B)`.
* `MMP.Mori.existsUnique_comp_eq_of_isBirationalMorphism_of_forall_curve`: the factorization.

## Implementation notes

The decomposition `B = E + H` is recorded by the finite set `𝓔` of prime divisors carrying
`E`; every component of `S` not in `𝓔` is a component of `H`. The log discrepancy is the
relation `MMP.Flips.IsLogDiscrepancy`, so the conclusion bounds every value it relates to `ν`.
The base field `k` is assumed perfect (the source works over `ℂ`): over an imperfect field a
divisorial valuation ring need not be smooth over `k`, and the order of a top form along it is
not the order computed by the snc formula.

The source states the factorization for a proper birational morphism `p` of complex varieties
with `X` normal and `Y` a variety. The argument uses that `p` is proper with `𝒪_X ≅ p_* 𝒪_W`
(Zariski's main theorem gives this in the birational normal case) and that `X` is of finite
type over a field, so that closed points and curves see every fibre. The statement keeps the
source's `Y` separated, over an arbitrary base `S` with `p ≫ sX = q ≫ sY`; the argument does
not use these. An integral curve `C ⊆ W` is recorded by its underlying set: an irreducible
closed subset of `W` of topological Krull dimension one. That `p(C)` is a point is the statement
that `p '' C` is a singleton. The curves used are the closures `{y}⁻` of points `y` specialising
to a closed point with no point strictly in between; constancy of `q` along a curve is compared
through closures `{q x}⁻` in `Y`, so no closedness of points of `Y` is needed.

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 4.12.1.2
-/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

/-! ### A lower bound for log discrepancies -/

namespace MMP.Flips

open MMP.Mori

/-- Let `b i ≤ 1` on `𝓔` and `c ≤ 1 - b i` on `s \ 𝓔`, with `0 ≤ c ≤ 1`. If `n i ≠ 0` wherever
`p i` holds on `s`, and fewer members of `𝓔` satisfy `p` than `l` plus the members of `s` that
do, then `c ≤ l + ∑ i ∈ s, n i * (1 - b i)`. -/
private lemma le_add_sum_of_card_filter_lt {ι : Type*} {s 𝓔 : Finset ι}
    {p : ι → Prop} [DecidablePred p] {b : ι → ℝ} {n : ι → ℕ} {l : ℕ} {c : ℝ}
    (he : ∀ i ∈ 𝓔, b i ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hh : ∀ i ∈ s, i ∉ 𝓔 → c ≤ 1 - b i)
    (hn : ∀ i ∈ s, n i = 0 → ¬ p i) (hcard : (𝓔.filter p).card < l + (s.filter p).card) :
    c ≤ l + ∑ i ∈ s, (n i : ℝ) * (1 - b i) := by
  have hterm : ∀ i ∈ s, 0 ≤ (n i : ℝ) * (1 - b i) := fun i hi => mul_nonneg (by positivity) <| by
    by_cases h : i ∈ 𝓔
    · linarith [he i h]
    · linarith [hh i hi h]
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · obtain ⟨i, hi, hiE⟩ := Finset.exists_mem_notMem_of_card_lt_card (by simpa using hcard)
    rw [Finset.mem_filter] at hi
    have hni : (1 : ℝ) ≤ n i := by
      exact_mod_cast Nat.one_le_iff_ne_zero.2 fun h => hn i hi.1 h hi.2
    have := Finset.single_le_sum hterm hi.1
    have := hh i hi.1 fun h => hiE (Finset.mem_filter.2 ⟨h, hi.2⟩)
    push_cast
    nlinarith
  · have : (1 : ℝ) ≤ l := by exact_mod_cast hl
    linarith [Finset.sum_nonneg hterm]

open Classical in
/-- **Lower bound for log discrepancies over an snc divisor.** Let `Y` be a smooth variety over a
perfect field `k`, `S` an snc divisor on `Y` and `B` an `ℝ`-divisor with `Supp B ⊆ Supp S`. Let
`𝓔` be a finite set of prime divisors with `coeff_P B ≤ 1` for `P ∈ 𝓔`, and `0 ≤ c ≤ 1` with
`1 - coeff_P B ≥ c` for every component `P` of `S` not in `𝓔`. If `ν` is a divisor over `Y` whose
center `Z` is contained in fewer members of `𝓔` than `codim_Y Z`, then every log discrepancy
`a_ℓ(ν, Y, B)` is `≥ c`. -/
@[mmp "lem_fa2_snc_log_discrepancy_lower_bound"]
public theorem le_logDiscrepancy_of_isSNCDivisor {k : Type u} [Field k] [PerfectField k]
    {Y : Scheme.{u}} (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    [CompactSpace Y] [LocallyOfFiniteType sY] (hY : Mori.IsVariety k sY) (hsm : IsSmoothScheme sY)
    {S : Divisor Y} (hS : IsSNCDivisor sY S) {B : RDivisor Y}
    (hBS : ∀ P, B.coeff P ≠ 0 → P ∈ S.support) {𝓔 : Finset (Mori.PrimeDivisor Y)}
    (he : ∀ P ∈ 𝓔, B.coeff P ≤ 1) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hh : ∀ P ∈ S.support, P ∉ 𝓔 → c ≤ 1 - B.coeff P) (ν : ProperDivisorOver k sY)
    (hcount : ((𝓔.filter fun P => (ν.center : Set Y) ⊆ P.support).card : ℕ∞) <
      codimension ν.center)
    {n : ℕ} {K : Divisor Y} {b : ℝ} (hb : IsLogDiscrepancy sY n K B ν.valuation b) :
    c ≤ b := by
  obtain ⟨l, m, hbeq, -, hm, hcod, -⟩ :=
    exists_logDiscrepancy_eq_add_sum_of_isSNCDivisor sY hY hsm hS hBS ν hb
  rw [hbeq]
  exact le_add_sum_of_card_filter_lt he hc0 hc1 hh (fun P hP => (hm P hP).1)
    (by exact_mod_cast hcount.trans_le hcod)

end MMP.Flips

/-! ### Factorization through a contraction by contracted curves -/

namespace MMP.Mori

open Topology MMP.Fourfold

section Curves

variable {k : Type u} [Field k] {X : Scheme.{u}}

/-- The closure of a point has the dimension of its reduced closed subscheme. -/
private theorem topologicalKrullDim_closure_singleton_eq_curveSubschemeAt (y : X) :
    topologicalKrullDim (closure ({y} : Set X)) = topologicalKrullDim (curveSubschemeAt y) := by
  let e := (curveSubschemeAtι y).isClosedEmbedding.isEmbedding.toHomeomorph
  let e' := e.trans (Homeomorph.setCongr (range_curveSubschemeAtι y))
  exact (IsHomeomorph.topologicalKrullDim_eq e' e'.isHomeomorph).symm

/-- **Curves through a point avoiding a closed set.** Let `X` be locally Noetherian and locally
of finite type over a field, `p` a closed point, `η ⤳ p` and `Z ∋ p` a closed subset not
containing `η`. There is a point `y` with `η ⤳ y ⤳ p`, `y ∉ Z` and `{y}⁻` of dimension one. -/
private theorem exists_curve_of_specializes (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX]
    [IsLocallyNoetherian X] {η p : X} (hηp : η ⤳ p) (hp : IsClosed ({p} : Set X)) {Z : Set X}
    (hZ : IsClosed Z) (hpZ : p ∈ Z) (hηZ : η ∉ Z) :
    ∃ y : X, η ⤳ y ∧ y ⤳ p ∧ y ∉ Z ∧ topologicalKrullDim (closure ({y} : Set X)) = 1 := by
  classical
  set R := X.presheaf.stalk p
  set g := X.fromSpecStalk p
  obtain ⟨Q, hQ⟩ := Stacks.Chow.exists_fromSpecStalk_eq hηp
  have hT : IsClosed (g ⁻¹' Z : Set (PrimeSpectrum R)) := hZ.preimage g.continuous
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp hT
  have hQT : ¬ ((I : Set R) ⊆ Q.asIdeal) := fun h => hηZ (hQ ▸ hI.ge h)
  obtain ⟨a, haI, haQ⟩ := Set.not_subset.mp hQT
  have hgM : g (IsLocalRing.closedPoint R) = p := Scheme.fromSpecStalk_closedPoint
  have hQM : Q.asIdeal < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal Q.isPrime.ne_top) fun h => hηZ ?_
    rw [← hQ, show Q = IsLocalRing.closedPoint R from PrimeSpectrum.ext h,
      Scheme.fromSpecStalk_closedPoint]
    exact hpZ
  obtain ⟨q, hq, hQq, hqM, haq, himm⟩ := exists_isPrime_le_lt_notMem_of_lt hQM haQ
  set qpt : PrimeSpectrum R := ⟨q, hq⟩
  have hyZ : g qpt ∉ Z := by
    intro h
    have h' : qpt ∈ (g ⁻¹' Z : Set (PrimeSpectrum R)) := h
    rw [hI] at h'
    exact haq (h' haI)
  have hyp : g qpt ⤳ p := Stacks.Chow.specializes_fromSpecStalk p qpt
  refine ⟨g qpt, ?_, hyp, hyZ, ?_⟩
  · rw [← hQ]
    exact ((PrimeSpectrum.le_iff_specializes Q qpt).mp hQq).map g.continuous
  · rw [topologicalKrullDim_closure_singleton_eq_curveSubschemeAt]
    refine topologicalKrullDim_curveSubschemeAt_eq_one sX hyp
      (fun h => hyZ (by rw [h]; exact hpZ)) hp fun z hyz hzp => ?_
    obtain ⟨r, rfl⟩ := Stacks.Chow.exists_fromSpecStalk_eq hzp
    have hle : r ≤ qpt := (Stacks.Chow.fromSpecStalk_le_iff p).mp hyz
    have hqr : q ≤ r.asIdeal := (PrimeSpectrum.le_iff_specializes qpt r).mpr hle
    rcases eq_or_lt_of_le hqr with h | h
    · left
      congr 1
      exact PrimeSpectrum.ext h.symm
    · right
      have := himm r.asIdeal r.isPrime h (IsLocalRing.le_maximalIdeal r.isPrime.ne_top)
      rw [show r = IsLocalRing.closedPoint R from PrimeSpectrum.ext this]
      exact hgM

end Curves

section Fibres

variable {k : Type u} [Field k] {U V Z : Scheme.{u}} (sU : U ⟶ Spec (.of k))
  [LocallyOfFiniteType sU] [IsLocallyNoetherian U] {g : U ⟶ V} {h : U ⟶ Z}
  (hcurve : ∀ C : Set U, IsClosed C → IsIrreducible C → topologicalKrullDim C = 1 →
      (g.base '' C).Subsingleton → (h.base '' C).Subsingleton)
  (hgc : IsClosedMap g)

/-- A closed subset of a quasi-sober space contained in a Noetherian subspace is the union of the
closures of finitely many of its points. -/
private theorem exists_finite_eq_biUnion_closure {T : Type*} [TopologicalSpace T] [QuasiSober T]
    {F N : Set T} [NoetherianSpace N] (hF : IsClosed F) (hFN : F ⊆ N) :
    ∃ E : Set T, E.Finite ∧ F = ⋃ η ∈ E, closure ({η} : Set T) := by
  classical
  rcases isEmpty_or_nonempty T with hT | hT
  · exact ⟨∅, Set.finite_empty, by simp [Set.eq_empty_of_isEmpty F]⟩
  obtain ⟨S, hSf, -, hSi, hS⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (hF.preimage continuous_subtype_val : IsClosed ((↑) ⁻¹' F : Set N))
  have hgen : ∀ t ∈ S, ∃ η : T, closure {η} = closure ((↑) '' t : Set T) := fun t ht =>
    QuasiSober.sober ((hSi t ht).image _ continuous_subtype_val.continuousOn).closure
      isClosed_closure
  choose! η hη using hgen
  have hsub : ∀ t ∈ S, closure ((↑) '' t : Set T) ⊆ F := fun t ht =>
    closure_minimal (by
      rintro _ ⟨x, hx, rfl⟩
      have : x ∈ ((↑) ⁻¹' F : Set N) := hS ▸ Set.mem_sUnion_of_mem hx ht
      exact this) hF
  refine ⟨η '' S, hSf.image _, subset_antisymm (fun x hx => ?_) (Set.iUnion₂_subset ?_)⟩
  · have hx' : (⟨x, hFN hx⟩ : N) ∈ ((↑) ⁻¹' F : Set N) := hx
    rw [hS] at hx'
    obtain ⟨t, ht, hxt⟩ := hx'
    exact Set.mem_biUnion (Set.mem_image_of_mem _ ht)
      ((hη t ht).symm ▸ subset_closure ⟨_, hxt, rfl⟩)
  · rintro _ ⟨t, ht, rfl⟩
    exact (hη t ht).symm ▸ hsub t ht

include sU hcurve in
/-- If `{y}⁻` lies in a fibre of `g`, then `h y = h p` for every closed point `p` of `{y}⁻`. -/
private theorem apply_eq_of_specializes {w : V} {y p : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hyp : y ⤳ p) (hp : IsClosed ({p} : Set U)) :
    h y = h p := by
  by_contra hne
  have hZ : IsClosed (h ⁻¹' closure {h p}) := isClosed_closure.preimage h.continuous
  have hyZ : y ∉ h ⁻¹' closure {h p} := fun H =>
    hne ((hyp.map h.continuous).antisymm (specializes_iff_mem_closure.mpr H)).eq
  obtain ⟨c, hyc, hcp, hcZ, hc⟩ := exists_curve_of_specializes sU hyp hp hZ
    (subset_closure rfl) hyZ
  have hcy : closure ({c} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hyc))
      isClosed_closure
  have hgC : (g.base '' closure {c}).Subsingleton := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have h1 := hy (hcy ha)
    have h2 := hy (hcy hb)
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at h1 h2
    exact h1.trans h2.symm
  have := hcurve _ isClosed_closure isIrreducible_singleton.closure hc hgC
    ⟨p, specializes_iff_mem_closure.mp hcp, rfl⟩ ⟨c, subset_closure rfl, rfl⟩
  exact hcZ (show h c ∈ closure {h p} from this ▸ subset_closure rfl)

include sU hcurve in
/-- If `{y}⁻` lies in a fibre of `g`, then `h` is constant on `{y}⁻`. -/
private theorem apply_eq_of_mem_closure [JacobsonSpace U] {w : V} {y x : U}
    (hy : closure ({y} : Set U) ⊆ g ⁻¹' {w}) (hx : x ∈ closure ({y} : Set U)) : h x = h y := by
  obtain ⟨p, hp, hpc⟩ := nonempty_inter_closedPoints (Z := closure ({x} : Set U))
    ⟨x, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  rw [mem_closedPoints_iff] at hpc
  have hxy : closure ({x} : Set U) ⊆ closure {y} :=
    closure_minimal (Set.singleton_subset_iff.mpr hx) isClosed_closure
  rw [apply_eq_of_specializes sU hcurve (hxy.trans hy) (specializes_iff_mem_closure.mpr hp) hpc,
    apply_eq_of_specializes sU hcurve hy (specializes_iff_mem_closure.mpr (hxy hp)) hpc]

include sU hcurve in
/-- Two points in a preconnected fibre of `g` that is a finite union of point closures have the
same image under `h`. -/
private theorem apply_eq_of_isPreconnected [JacobsonSpace U] {w : V} {E : Set U}
    (hE : E.Finite) (hF : g ⁻¹' {w} = ⋃ η ∈ E, closure ({η} : Set U))
    (hconn : _root_.IsPreconnected (g ⁻¹' {w})) {p q : U} (hp : g p = w) (hq : g q = w) :
    h p = h q := by
  have hsub : ∀ η ∈ E, closure ({η} : Set U) ⊆ g ⁻¹' {w} := fun η hη =>
    hF ▸ Set.subset_biUnion_of_mem (u := fun η => closure ({η} : Set U)) hη
  have hval : ∀ η ∈ E, ∀ x ∈ closure ({η} : Set U), h x = h η := fun η hη x hx =>
    apply_eq_of_mem_closure sU hcurve (hsub η hη) hx
  set A := ⋃ η ∈ {η ∈ E | h η = h p}, closure ({η} : Set U)
  set B := ⋃ η ∈ {η ∈ E | h η ≠ h p}, closure ({η} : Set U)
  have hA : IsClosed A := (hE.subset fun _ h => h.1).isClosed_biUnion fun _ _ => isClosed_closure
  have hB : IsClosed B := (hE.subset fun _ h => h.1).isClosed_biUnion fun _ _ => isClosed_closure
  have hcover : g ⁻¹' {w} ⊆ A ∪ B := by
    intro x hx
    rw [hF] at hx
    obtain ⟨η, hη, hxη⟩ := Set.mem_iUnion₂.mp hx
    by_cases hηp : h η = h p
    · exact Or.inl (Set.mem_biUnion ⟨hη, hηp⟩ hxη)
    · exact Or.inr (Set.mem_biUnion ⟨hη, hηp⟩ hxη)
  have hdisj : g ⁻¹' {w} ∩ (A ∩ B) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun x ⟨_, hxA, hxB⟩ => ?_
    obtain ⟨η, ⟨hη, hηp⟩, hxη⟩ := Set.mem_iUnion₂.mp hxA
    obtain ⟨η', ⟨hη', hη'p⟩, hxη'⟩ := Set.mem_iUnion₂.mp hxB
    exact hη'p ((hval η' hη' x hxη').symm.trans ((hval η hη x hxη).trans hηp))
  rcases isPreconnected_iff_subset_of_disjoint_closed.mp hconn _ _ hA hB hcover hdisj
    with hs | hs
  · obtain ⟨η, ⟨hη, hηp⟩, hqη⟩ := Set.mem_iUnion₂.mp (hs hq)
    exact ((hval η hη q hqη).trans hηp).symm
  · obtain ⟨η, ⟨hη, hηp⟩, hpη⟩ := Set.mem_iUnion₂.mp (hs hp)
    exact absurd (hval η hη p hpη).symm hηp

include sU hcurve hgc in
/-- `h` is constant on every fibre of `g`, when the fibres of `g` over closed points are
preconnected and are finite unions of point closures. -/
private theorem apply_eq_of_apply_eq [JacobsonSpace U]
    (hconn : ∀ v : V, _root_.IsPreconnected (g ⁻¹' {v}))
    (hfin : ∀ v : V, IsClosed ({v} : Set V) →
      ∃ E : Set U, E.Finite ∧ g ⁻¹' {v} = ⋃ η ∈ E, closure ({η} : Set U))
    {x x' : U} (hxx : g x = g x') : h x = h x' := by
  suffices H : ∀ x x' : U, g x = g x' → h x ⤳ h x' from
    (H x x' hxx).antisymm (H x' x hxx.symm) |>.eq
  intro x x' hxx
  by_contra hn
  have hC : IsClosed (h ⁻¹' closure {h x}) := isClosed_closure.preimage h.continuous
  have hx'O : x' ∈ (h ⁻¹' closure {h x})ᶜ := fun H => hn (specializes_iff_mem_closure.mpr H)
  have hx' : x' ∈ closure (closure {x'} ∩ closedPoints U) := by
    rw [JacobsonSpace.closure_inter_closedPoints isClosed_closure]
    exact subset_closure rfl
  obtain ⟨p, hpO, hpx', hpc⟩ := mem_closure_iff.mp hx' _ hC.isOpen_compl hx'O
  rw [mem_closedPoints_iff] at hpc
  have hgp : g p ∈ g '' closure {x} := by
    have hsub : closure {g x} ⊆ g '' closure {x} :=
      closure_minimal (Set.singleton_subset_iff.mpr ⟨x, subset_closure rfl, rfl⟩)
        (hgc _ isClosed_closure)
    refine hsub (specializes_iff_mem_closure.mp ?_)
    rw [hxx]
    exact (specializes_iff_mem_closure.mpr hpx').map g.continuous
  obtain ⟨q₀, hq₀, hgq₀⟩ := hgp
  have hwc : IsClosed ({g p} : Set V) := by
    have := hgc _ hpc
    rwa [Set.image_singleton] at this
  obtain ⟨q, ⟨hqx, hgq⟩, -⟩ := nonempty_inter_closedPoints (Z := closure {x} ∩ g ⁻¹' {g p})
    ⟨q₀, hq₀, hgq₀⟩ (isClosed_closure.inter (hwc.preimage g.continuous)).isLocallyClosed
  obtain ⟨E, hE, hF⟩ := hfin (g p) hwc
  have hpq : h q = h p := apply_eq_of_isPreconnected sU hcurve hE hF (hconn _) hgq rfl
  have hqC : h q ∈ closure {h x} :=
    specializes_iff_mem_closure.mp ((specializes_iff_mem_closure.mpr hqx).map h.continuous)
  exact hpO (show h p ∈ closure {h x} from hpq ▸ hqC)

end Fibres

/-- The fibre of a quasi-compact morphism with locally Noetherian source over a closed point is
the union of the closures of finitely many of its points. -/
private theorem exists_finite_preimage_singleton_eq_biUnion_closure {W X : Scheme.{u}}
    (p : W ⟶ X) [QuasiCompact p] [IsLocallyNoetherian W] {v : X} (hv : IsClosed ({v} : Set X)) :
    ∃ E : Set W, E.Finite ∧ p ⁻¹' {v} = ⋃ η ∈ E, closure ({η} : Set W) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hvV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ v) isOpen_univ
  have : CompactSpace (p ⁻¹ᵁ V : W.Opens) := isCompact_iff_compactSpace.mp <|
    QuasiCompact.isCompact_preimage (f := p) _ V.isOpen hV.isCompact
  have : IsNoetherian (p ⁻¹ᵁ V : W.Opens).toScheme := ⟨⟩
  have : NoetherianSpace ((p ⁻¹ᵁ V : W.Opens) : Set W) :=
    inferInstanceAs (NoetherianSpace (p ⁻¹ᵁ V : W.Opens).toScheme)
  exact exists_finite_eq_biUnion_closure (N := ((p ⁻¹ᵁ V : W.Opens) : Set W))
    (hv.preimage p.continuous) fun x (hx : p x = v) => show p x ∈ V from hx ▸ hvV

/-- **Curve criterion for factorization through a proper birational morphism.** Let
`p : W ⟶ X` be a proper birational morphism of varieties over a field `k`, with `X` normal, and
`q : W ⟶ Y` a morphism to a scheme separated over `S`, with `p ≫ sX = q ≫ sY`. If `q` maps to a
point every integral curve `C ⊆ W` (an irreducible closed subset of dimension one) that `p` maps
to a point, then there is a unique morphism `h : X ⟶ Y` with `p ≫ h = q`. -/
@[mmp "thm_mmp_birational_vertical_curve_factorization"]
public theorem existsUnique_comp_eq_of_isBirationalMorphism_of_forall_curve
    {k : Type u} [Field k] {S W X Y : Scheme.{u}}
    (kX : X ⟶ Spec (.of k)) (hX : AlgebraicGeometry.IsVariety k kX) [IsNormal X]
    {sX : X ⟶ S} {sY : Y ⟶ S} [IsSeparated sY]
    (p : W ⟶ X) (hW : AlgebraicGeometry.IsVariety k (p ≫ kX)) [IsProper p]
    (hp : IsBirationalMorphism p) (q : W ⟶ Y) (hpq : p ≫ sX = q ≫ sY)
    (hcurve : ∀ C : Set W, IsClosed C → IsIrreducible C → topologicalKrullDim C = 1 →
      (p.base '' C).Subsingleton → (q.base '' C).Subsingleton) :
    ∃! h : X ⟶ Y, p ≫ h = q := by
  have : LocallyOfFiniteType kX := hX.toLocallyOfFiniteType
  obtain ⟨-, -, hO, hconn, -⟩ := zariskiMain_of_isProper_of_isBirationalMorphism kX p hX hW hp
  have : IsIso p.c := by
    have : ∀ U : (X.Opens)ᵒᵖ, IsIso (p.c.app U) := fun U => hO U.unop
    exact NatIso.isIso_of_isIso_app p.c
  have : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian (p ≫ kX)
  have : JacobsonSpace W := LocallyOfFiniteType.jacobsonSpace (p ≫ kX)
  exact MMP.existsUnique_comp_eq_of_isIso_c p q fun x x' hxx =>
    apply_eq_of_apply_eq (p ≫ kX) hcurve p.isClosedMap
      (fun v => (hconn v).isPreconnected)
      (fun _ => exists_finite_preimage_singleton_eq_biUnion_closure p) hxx

end MMP.Mori
