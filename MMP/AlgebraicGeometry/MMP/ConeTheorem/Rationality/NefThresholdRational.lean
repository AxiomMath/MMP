module

public import MMP.AlgebraicGeometry.MMP.ConeTheorem.StripBaseLocusStabilizes
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripSectionsIrrational
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripBaseLocusDrop
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StableStripBaseLocus
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.StripAdaptedResolution
public import MMP.AlgebraicGeometry.MMP.ConeTheorem.Rationality.StripTieBreaker

/-!
# Rationality of the nef threshold

Let `(X, Δ, a, H)` be a rationality datum and let `r > 0` be the nef threshold of `H` with
respect to `K_X + Δ`, the largest real `t` with `H + t(K_X + Δ)` nef. Then `r` is rational.
Were `r` irrational, the base loci `L(p, q)` of `pH + qa(K_X + Δ)` would stabilize along the
strip `0 < aq - rp < 1` to a proper closed subset `Z ⊊ X`. A resolution adapted to a lattice
point of the strip, with a tie-breaking divisor `F` mapping into `Z`, produces nonzero sections
on `F` for a lattice point `(p', q')` further along the strip, whose base locus then cannot
contain the image of `F`, a contradiction.

## Main results

* `MMP.Mori.IsRationalityDatum.exists_rat_eq_of_isNefThreshold`: the nef threshold is rational.

## Implementation notes

Rationality of `r : ℝ` is stated as `∃ q : ℚ, (q : ℝ) = r`, the negation of `Irrational r`.

## References

* [J. Kollár, S. Mori, *Birational geometry of algebraic varieties*][KollarMori], Theorem 3.5
  and its proof in 3.4, Steps 4–10
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

namespace MMP.Mori

/-- For a rationality datum, the strip divisor `p'H + q'⌊a(K_X + Δ)⌋` is Cartier. -/
private theorem IsRationalityDatum.isCartier_stripDivisor {k : Type} [Field k]
    {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X]
    {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ} {K : Divisor X} {Δ : QDivisor X} {a : ℤ}
    {H : Divisor X} (h : IsRationalityDatum sX n K Δ a H) (p' q' : ℤ) :
    (stripDivisor K Δ a H p' q').IsCartier := by
  obtain ⟨D₀, hD₀, hD₀c⟩ := h.isCartierDivisor
  rw [stripDivisor, ← hD₀,
    (DivisorWithCoeffs.ext' fun _ => by simp : (Divisor.toQDivisor D₀).roundDown = D₀)]
  exact (h.isCartier_H.zsmul p').add (hD₀c.zsmul q')

/-- **Rationality of the nef threshold** (Kollár–Mori, Theorem 3.5). Let `(X, Δ, a, H)` be a
rationality datum and `r > 0` the nef threshold of `H` with respect to `K_X + Δ`. Then `r` is
rational. -/
@[mmp "thm_km3b_rationality_free_rational"]
public theorem IsRationalityDatum.exists_rat_eq_of_isNefThreshold {k : Type} [Field k]
    [IsAlgClosed k] [CharZero k] {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]
    [IsNormal X] [CompactSpace X] {sX : X ⟶ Spec (.of k)} [QuasiCompact sX] {n : ℕ}
    {K : Divisor X} {Δ : QDivisor X} {a : ℤ} {H : Divisor X}
    (hD : IsRationalityDatum sX n K Δ a H) {r : ℝ}
    (hr : QDivisor.IsNefThreshold k sX (Divisor.toQDivisor H) (Divisor.toQDivisor K + Δ) r)
    (hr0 : 0 < r) :
    ∃ q : ℚ, (q : ℝ) = r := by
  by_contra hrat
  have hirr : Irrational r := fun ⟨q, hq⟩ => hrat ⟨q, hq⟩
  have ha : 0 < a := hD.pos
  -- the stable base locus `Z ≠ X` of the `(r, 1)`-strip
  obtain ⟨Z, hZ⟩ := hD.exists_isStableStripBaseLocus hr hr0 one_pos
  have hZtop : Z ≠ ⊤ := hD.ne_top_of_isStableStripBaseLocus hr hr0
    (fun u v _ _ h => hirr ⟨(u : ℚ) / v, by push_cast; exact h.symm⟩) hZ
  obtain ⟨N, hN⟩ := hZ
  -- a lattice point `(p, q)` of the strip with `p, q ≥ N`
  obtain ⟨p, q, hNp, hNq, hpq₀, hpq₁⟩ := Positivity.exists_strip_point_of_irrational ha hr0
    (fun u v hu h => hirr ⟨(a * v : ℚ) / u, by
      have hu' : (u : ℝ) ≠ 0 := by exact_mod_cast hu.ne'
      push_cast
      rw [div_eq_iff hu']
      linarith⟩) one_pos (max N 1)
  have hp : 0 < p := by omega
  have hq : 0 < q := by omega
  replace hNp : N ≤ p := (le_max_left _ _).trans hNp
  replace hNq : N ≤ q := (le_max_left _ _).trans hNq
  have hLZ : stripBaseLocus K Δ a H p q = Z := hN p q hNp hNq hpq₀ hpq₁
  -- a nonzero section of `pH + qa(K_X + Δ)`
  have hσ : ∃ σ : (stripDivisor K Δ a H p q).divisorialSubmodule ⊤, σ ≠ 0 := by
    by_contra hno
    push Not at hno
    refine hZtop (hLZ ▸ eq_top_iff.mpr fun x _ => ?_)
    exact (Divisor.mem_baseLocus_iff _ x).mpr fun σ hσ => absurd (hno σ) hσ
  have hL0 : stripBaseLocus K Δ a H p q ≠ ⊥ := hD.stripBaseLocus_ne_bot hr hp hpq₀
  -- a `(p, q)`-adapted resolution with a tie-breaker `(j₀, c)`
  obtain ⟨Y, _, _, _, f, s, F, aj, pj, rj, hres⟩ :=
    hD.exists_isStripAdaptedResolution hr hp hq hpq₀ hpq₁ hσ
  obtain ⟨pj', j₀, c, htb⟩ := hres.exists_isStripTieBreaker hr hpq₀ hpq₁ hL0
  -- `f(F_{j₀}) ⊆ L(p, q) = Z`
  have hFZ : f '' (F j₀).support ⊆ (Z : Set X) := by
    rw [← hLZ, htb.toIsStripAdaptedResolution.stripBaseLocus_eq_image]
    exact Set.image_mono (Set.subset_biUnion_of_mem (u := fun j => (F j).support)
      (show j₀ ∈ {j | 0 < rj j} from htb.pos_r))
  -- restricted sections at `(p', q')` further along the strip
  obtain ⟨p', q', hNp', hNq', hp', hq', h₀, h₁, hsec⟩ :=
    htb.exists_nontrivial_cohomologyOverField_restrict hr hr0 hirr hpq₀ N
  -- a pull-back of `p'H + q'a(K_X + Δ)` along `f`
  haveI : AlgebraicGeometry.IsProjectiveVariety k (f ≫ sX) := htb.isProjectiveVariety
  haveI : IsIntegral Y := AlgebraicGeometry.IsVariety.toIsIntegral (k := k) (f := f ≫ sX)
  haveI : IsDominant f := htb.isLogResolution.isBirationalMorphism.isDominant
  have hM : ∀ Z : irreducibleComponents Y,
      f (componentGenericPoint Y Z) ∉ (stripDivisor K Δ a H p' q').supp := fun Z =>
    MMP.Threefold.Resolution.map_componentGenericPoint_notMem_supp_of_isDominant' f _ Z
  obtain ⟨B', hB'⟩ := (hD.isCartier_stripDivisor p' q').exists_isPullback hM
  have hdrop := htb.not_image_subset_stripBaseLocus hr hpq₀ hp' hq' h₁.le hB' (hsec hM B' hB')
  rw [hN p' q' hNp' hNq' h₀ (h₁.trans hpq₁)] at hdrop
  exact hdrop hFZ

end MMP.Mori
