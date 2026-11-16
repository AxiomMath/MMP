module

public import MMP.AlgebraicGeometry.Singularities.TerminalThreefoldEchoFinite
public import MMP.AlgebraicGeometry.MMP.Fourfold.EchoLogDiscrepancy

/-!
# Valuations below log discrepancy two on a terminal threefold

Let `(Y, Θ)` be a terminal pair on a projective `ℚ`-factorial complex threefold `Y`, and let
`L = {S_1, …, S_m}` be distinct prime divisors with `Supp Θ ⊆ ⋃_h S_h`, so `Θ = ∑_h b_h S_h`
with every `b_h < 1`. This file locates the normalized divisorial valuations `ξ` of `ℂ(Y)` with
`a(ξ; Y, Θ) < 2` according to their centre `c_Y(ξ)`.

Only finitely many exceptional such valuations are not echoes
(`MMP.Fourfold.finite_setOf_not_isEcho`). A valuation centred on a curve or on a closed point is
exceptional, and an echo is centred on a curve. Hence:

* for a fixed curve `V`, the valuations with centre `V` are the finitely many non-echoes together
  with the echoes of the labels through `V`; the echo of order `j` is unique and has
  `a = 1 + j (1 - b_h)`, which is `< 2` for only finitely many `j`;
* outside the finitely many curves that are centres of non-echoes, every valuation centred on a
  curve `V` is an echo of the unique label through `V`, and `η_V` lies in the one-label smooth
  locus;
* the valuations centred on closed points are among the finitely many non-echoes.

## Main results

* `MMP.Fourfold.finite_setOf_isCentre`: for a curve `V`, the valuations with centre `V` and
  `a < 2` form a finite set.
* `MMP.Fourfold.exists_finite_forall_isEcho_of_isCentre`: off a finite set of curves, every
  valuation centred on a curve with `a < 2` is an echo of order `j ≥ 1` of the unique label
  through the curve, with `a = 1 + j (1 - b_h)`.
* `MMP.Fourfold.finite_setOf_isCentre_singleton`: the valuations centred on a closed point with
  `a < 2` form a finite set.

## Implementation notes

* The labels are a finite set `L` of prime divisors and `Supp Θ ⊆ ⋃_h S_h` is
  `Θ.support ⊆ L`, as in `MMP.Fourfold.finite_setOf_not_isEcho`; `b_h` is `Θ.coeff S_h`.
* "`ξ` is a normalized divisorial valuation with `c_Y(ξ) = V`" is `MMP.Intersection.IsCentre`,
  which already presents `ξ` as `ord_E` for a divisor over `Y` with proper structure map.
* An irreducible closed curve is an irreducible closed subset `V` with
  `topologicalKrullDim V = 1`; a closed point as centre is a centre equal to a singleton `{y}`.
* `a(ξ; Y, Θ) < 2` reads: `ξ` has some log discrepancy `a < 2`
  (`MMP.Fourfold.HasLogDiscrepancy`).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace MMP.Mori

attribute [-instance] AlgebraicGeometry.IsVariety.toIsIntegral

namespace MMP.Fourfold

section Helpers

variable {Y : Scheme.{0}} {sY : Y ⟶ Spec (.of ℂ)} [IsIntegral Y]

/-- On a klt pair every boundary coefficient is `< 1`: the log discrepancy `1 - b_P` of a prime
divisor `P` of `Y` is positive. -/
private theorem coeff_lt_one_of_isKltPair [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    (hΘ : IsKltPair sY Θ) (P : MMP.Mori.PrimeDivisor Y) : Θ.coeff P < 1 := by
  obtain ⟨hvar, n, K, hK, -⟩ := id hΘ.1.isPair
  obtain ⟨a, ha⟩ := MMP.Positivity.IsPair.exists_isDiscrepancy hΘ.1.isPair hK
    (DivisorOver.ofPrimeDivisor ℂ hvar P)
  have hp : IsProper (DivisorOver.ofPrimeDivisor ℂ hvar P).f := by
    change IsProper (𝟙 Y); infer_instance
  have h := hΘ.2 n _ _ (MMP.Threefold.Bridges.isLogDiscrepancy_one_add_of_isDiscrepancy ha hp)
  rw [IsDiscrepancy.eq_neg_coeff_of_ofPrimeDivisor hvar ha] at h
  push_cast at h
  exact_mod_cast (by linarith : ((Θ.coeff P : ℚ) : ℝ) < 1)

/-- A divisorial valuation has at most one centre. -/
private theorem isCentre_unique (hX : MMP.Mori.IsVariety ℂ sY)
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))} {V V' : IrreducibleCloseds Y}
    (hV : MMP.Intersection.IsCentre ℂ sY ξ V) (hV' : MMP.Intersection.IsCentre ℂ sY ξ V') :
    V = V' := by
  obtain ⟨D, -, hD, rfl⟩ := hV
  obtain ⟨D', -, hD', rfl⟩ := hV'
  exact MMP.Positivity.DivisorOver.center_eq_of_valuation_eq hX (hD.symm.trans hD')

/-- The log discrepancy of a valuation is unique. -/
private theorem HasLogDiscrepancy.unique [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))} {a a' : ℝ}
    (h : HasLogDiscrepancy sY Θ ξ a) (h' : HasLogDiscrepancy sY Θ ξ a') : a = a' := by
  obtain ⟨n, D, hD, h⟩ := h
  obtain ⟨n', D', hD', h'⟩ := h'
  exact MMP.Threefold.Bridges.IsLogDiscrepancy.eq_of_valuation_eq h h' (hD.trans hD'.symm)

/-- On a variety of dimension three, a curve has codimension two. -/
private theorem codimension_eq_two [LocallyOfFiniteType sY] (hdim : topologicalKrullDim Y = 3)
    {V : IrreducibleCloseds Y} (hV : topologicalKrullDim (V : Set Y) = 1) :
    codimension V = 2 := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY
    V.isIrreducible.genericPoint
  rw [IsIrreducible.closure_genericPoint V.isIrreducible V.isClosed, hdim, hV] at h
  rw [MMP.Flips.codimension_eq_coheight_genericPoint]
  generalize Order.coheight V.isIrreducible.genericPoint = c at h ⊢
  have h' : (1 + c : ℕ∞) = 3 := WithBot.coe_injective (by rw [WithBot.coe_add]; exact h)
  induction c using ENat.recTopCoe with
  | top => simp at h'
  | coe n =>
    have : 1 + n = 3 := by exact_mod_cast h'
    norm_cast
    omega

/-- On a threefold, a divisorial valuation centred on a curve is exceptional. -/
private theorem isExceptionalValuation_of_isCentre [LocallyOfFiniteType sY]
    (hdim : topologicalKrullDim Y = 3) {V : IrreducibleCloseds Y}
    (hV : topologicalKrullDim (V : Set Y) = 1)
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (hC : MMP.Intersection.IsCentre ℂ sY ξ V) :
    MMP.Intersection.IsExceptionalValuation ℂ sY ξ := by
  obtain ⟨D, hD, hv, rfl⟩ := hC
  exact ⟨D, hD, hv, (codimension_eq_two (sY := sY) hdim hV).ge⟩

/-- For a label `S`, the echoes of `S` at `V` with log discrepancy `< 2` are finitely many: the
echo of order `j` is unique and has log discrepancy `1 + j (1 - b_S)`, which is `< 2` only for
`j < 1 / (1 - b_S)`. -/
private theorem finite_setOf_isEcho [IsLocallyNoetherian Y] [IsNormal Y] {Θ : QDivisor Y}
    (hΘ : IsKltPair sY Θ) {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L)
    (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) :
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      (∃ j, IsEcho sY L S V j ξ) ∧ ∃ a < 2, HasLogDiscrepancy sY Θ ξ a}.Finite := by
  have hb : (Θ.coeff S : ℝ) < 1 := by exact_mod_cast coeff_lt_one_of_isKltPair hΘ S
  refine ((Finset.range ⌈1 / (1 - (Θ.coeff S : ℝ))⌉₊).finite_toSet.biUnion
    (t := fun j => {ξ | IsEcho sY L S V j ξ}) fun j _ => ?_).subset ?_
  · refine Set.Subsingleton.finite fun ξ hξ ξ' hξ' => ?_
    obtain ⟨hY, hdim, hS, hVS, hV, hη, hj, -⟩ := id hξ
    exact ((existsUnique_isEcho hY hdim hS hVS hV hη).1 j hj).unique hξ hξ'
  · rintro ξ ⟨⟨j, hξ⟩, a, ha, hξa⟩
    have h := HasLogDiscrepancy.unique hξa
      (hξ.hasLogDiscrepancy hΘ.1 hsupp fun S' _ => coeff_lt_one_of_isKltPair hΘ S')
    exact Set.mem_biUnion (x := j)
      (Finset.mem_range.2 (Nat.lt_ceil.2 ((lt_div_iff₀ (sub_pos.2 hb)).2 (by linarith)))) hξ

/-- The label of an echo at `V` is the only label containing `V`: the generic point of `V` lies
in the one-label smooth locus. -/
private theorem eq_of_isEcho_of_subset {L : Finset (MMP.Mori.PrimeDivisor Y)}
    {S S' : MMP.Mori.PrimeDivisor Y} {V : IrreducibleCloseds Y} {j : ℕ}
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ))}
    (he : IsEcho sY L S V j ξ) (hS' : S' ∈ L) (hVS' : (V : Set Y) ⊆ S'.support) : S' = S := by
  have hη (T : MMP.Mori.PrimeDivisor Y) (hT : (V : Set Y) ⊆ T.support) :
      V.isIrreducible.genericPoint ∈ T.support :=
    hT (V.isClosed.closure_subset V.isIrreducible.isGenericPoint_genericPoint_closure.mem)
  exact eq_of_mem_oneLabelSmoothLocus he.2.2.2.2.2.1 hS' he.2.2.1 (hη S' hVS') (hη S he.2.2.2.1)

end Helpers

/-- A one-point subspace has Krull dimension zero. -/
private theorem topologicalKrullDim_singleton {X : Type*} [TopologicalSpace X] (y : X) :
    topologicalKrullDim ({y} : Set X) = 0 := by
  have : Nonempty (IrreducibleCloseds ({y} : Set X)) :=
    ⟨⟨closure {⟨y, rfl⟩}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact (topologicalKrullDim_zero_of_discreteTopology _).antisymm Order.krullDim_nonneg

/-- On an integral scheme of dimension `n`, locally of finite type over a field, a point whose
closure is a single point has coheight `n`. -/
private theorem coheight_eq_of_closure_eq_singleton {k : Type*} [Field k] {Y : Scheme}
    (sY : Y ⟶ Spec (.of k)) [IsIntegral Y] [LocallyOfFiniteType sY] {n : ℕ}
    (hdim : topologicalKrullDim Y = n) {x y : Y} (hx : closure {x} = ({y} : Set Y)) :
    Order.coheight x = n := by
  have h := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sY x
  rw [hx, hdim, topologicalKrullDim_singleton, zero_add] at h
  exact_mod_cast h

/-- **Finitely many valuations below log discrepancy two at a fixed curve.** Let `(Y, Θ)` be a
terminal pair on a projective `ℚ`-factorial complex threefold `Y`, and `L` a finite set of prime
divisors containing the support of `Θ`. For every irreducible closed curve `V ⊆ Y`, the
normalized divisorial valuations `ξ` of `ℂ(Y)` with centre `V` (`MMP.Intersection.IsCentre`) and
`a(ξ; Y, Θ) < 2` form a finite set: they are the non-echoes of
`MMP.Fourfold.finite_setOf_not_isEcho` and, for each label through `V`, finitely many echoes. -/
@[mmp "lem_mmp_indexd_echoes_curve"]
public theorem finite_setOf_isCentre
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L)
    (V : IrreducibleCloseds Y) (hV : topologicalKrullDim (V : Set Y) = 1) :
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      MMP.Intersection.IsCentre ℂ sY ξ V ∧ ∃ a < 2, HasLogDiscrepancy sY Θ ξ a}.Finite := by
  have : LocallyOfFiniteType sY := hY.toIsVariety.toLocallyOfFiniteType
  refine ((finite_setOf_not_isEcho sY hY hQ hdim hΘ hsupp).union (L.finite_toSet.biUnion
    fun S _ => finite_setOf_isEcho hΘ.1 hsupp S V)).subset ?_
  rintro ξ ⟨hC, hξa⟩
  by_cases he : ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
      IsEcho sY L S V j ξ
  · obtain ⟨S, V', j, hξ⟩ := he
    obtain rfl := isCentre_unique hY.toIsVariety hξ.2.2.2.2.2.2.2.1 hC
    exact Or.inr (Set.mem_biUnion (x := S) hξ.2.2.1 ⟨⟨j, hξ⟩, hξa⟩)
  · obtain ⟨D, hp, hD, -⟩ := id hC
    exact Or.inl ⟨⟨D, hp, hD⟩, isExceptionalValuation_of_isCentre hdim hV hC, hξa, he⟩

/-- **Generic curve centres below log discrepancy two are echoes.** Let `(Y, Θ)` be a terminal
pair on a projective `ℚ`-factorial complex threefold `Y`, and `L` a finite set of prime divisors
containing the support of `Θ`. There is a finite set `𝒮` of irreducible curves of `Y` such that
for every irreducible curve `V ∉ 𝒮` and every normalized divisorial valuation `ξ` of `ℂ(Y)` with
centre `V` and `a(ξ; Y, Θ) < 2`, the generic point of `V` lies in the one-label smooth locus
`MMP.Fourfold.oneLabelSmoothLocus L`, a unique label `S ∈ L` contains `V`, and `ξ` is an echo
(`MMP.Fourfold.IsEcho`) of some order `j ≥ 1` of `S` at `V` with log discrepancy
`1 + j (1 - Θ(S))`. The set `𝒮` consists of the curves that are centres of the finitely many
non-echoes of `MMP.Fourfold.finite_setOf_not_isEcho`. -/
@[mmp "lem_mmp_indexd_echoes_generic"]
public theorem exists_finite_forall_isEcho_of_isCentre
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    ∃ 𝒮 : Set (IrreducibleCloseds Y), 𝒮.Finite ∧
      (∀ V ∈ 𝒮, topologicalKrullDim (V : Set Y) = 1) ∧
      ∀ V : IrreducibleCloseds Y, topologicalKrullDim (V : Set Y) = 1 → V ∉ 𝒮 →
        ∀ ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)),
          MMP.Intersection.IsCentre ℂ sY ξ V → (∃ a < 2, HasLogDiscrepancy sY Θ ξ a) →
            V.isIrreducible.genericPoint ∈ oneLabelSmoothLocus L ∧
              ∃ S ∈ L, (V : Set Y) ⊆ S.support ∧
                (∀ S' ∈ L, (V : Set Y) ⊆ S'.support → S' = S) ∧
                ∃ j : ℕ, 1 ≤ j ∧ IsEcho sY L S V j ξ ∧
                  HasLogDiscrepancy sY Θ ξ (1 + j * (1 - (Θ.coeff S : ℝ))) := by
  have hX := hY.toIsVariety
  have : LocallyOfFiniteType sY := hX.toLocallyOfFiniteType
  set F := {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      MMP.Intersection.IsNormalizedDivisorialValuation ℂ sY ξ ∧
        MMP.Intersection.IsExceptionalValuation ℂ sY ξ ∧
        (∃ a < 2, HasLogDiscrepancy sY Θ ξ a) ∧
        ¬ ∃ (S : MMP.Mori.PrimeDivisor Y) (V : IrreducibleCloseds Y) (j : ℕ),
          IsEcho sY L S V j ξ}
  have hF : F.Finite := finite_setOf_not_isEcho sY hY hQ hdim hΘ hsupp
  refine ⟨{V | topologicalKrullDim (V : Set Y) = 1 ∧ ∃ ξ ∈ F, MMP.Intersection.IsCentre ℂ sY ξ V},
    (hF.biUnion fun ξ _ => Set.Subsingleton.finite (s := {V | MMP.Intersection.IsCentre ℂ sY ξ V})
      fun _ hV _ hV' => isCentre_unique hX hV hV').subset fun V ⟨_, ξ, hξ, hV⟩ =>
        Set.mem_biUnion hξ hV, fun V hV => hV.1, ?_⟩
  intro V hV hVS ξ hC ha
  obtain ⟨S, V', j, he⟩ : ∃ S V' j, IsEcho sY L S V' j ξ := by
    by_contra h
    obtain ⟨D, hD, hv, -⟩ := id hC
    exact hVS ⟨hV, ξ, ⟨⟨D, hD, hv⟩, isExceptionalValuation_of_isCentre hdim hV hC, ha, h⟩, hC⟩
  obtain rfl : V' = V := isCentre_unique hX he.2.2.2.2.2.2.2.1 hC
  exact ⟨he.2.2.2.2.2.1, S, he.2.2.1, he.2.2.2.1, fun _ => eq_of_isEcho_of_subset he, j,
    he.2.2.2.2.2.2.1, he,
    he.hasLogDiscrepancy hΘ.1.1 hsupp fun S' _ => coeff_lt_one_of_isKltPair hΘ.1 S'⟩

/-- **Point-centred valuations below log discrepancy two.** Let `(Y, Θ)` be a terminal pair on a
projective `ℚ`-factorial complex threefold `Y`, and `L` a finite set of prime divisors containing
the support of `Θ`. Then the normalized divisorial valuations `ξ` of `ℂ(Y)` whose centre on `Y`
is a closed point and with `a(ξ; Y, Θ) < 2` form a finite set. Such a `ξ` is exceptional (a
closed point of a threefold has codimension three) and not an echo (an echo is centred on a
curve), so it is one of the non-echoes of `MMP.Fourfold.finite_setOf_not_isEcho`. -/
@[mmp "lem_mmp_indexd_echoes_points"]
public theorem finite_setOf_isCentre_singleton
    {Y : Scheme.{0}} (sY : Y ⟶ Spec (.of ℂ)) [IsIntegral Y] [IsLocallyNoetherian Y] [IsNormal Y]
    (hY : MMP.Mori.IsProjectiveVariety ℂ sY) (hQ : IsQFactorial sY)
    (hdim : topologicalKrullDim Y = 3)
    {Θ : MMP.Mori.QDivisor Y} (hΘ : IsKltTerminalPair sY Θ)
    {L : Finset (MMP.Mori.PrimeDivisor Y)} (hsupp : Θ.support ⊆ L) :
    {ξ : Valuation Y.functionField (WithZero (Multiplicative ℤ)) |
      (∃ (Z : IrreducibleCloseds Y) (y : Y),
          MMP.Intersection.IsCentre ℂ sY ξ Z ∧ (Z : Set Y) = {y}) ∧
        ∃ a < 2, HasLogDiscrepancy sY Θ ξ a}.Finite := by
  have : LocallyOfFiniteType sY := hY.toIsVariety.toLocallyOfFiniteType
  refine (finite_setOf_not_isEcho sY hY hQ hdim hΘ hsupp).subset ?_
  rintro ξ ⟨⟨Z, y, ⟨D, hD, hξ, hZ⟩, hZy⟩, ha⟩
  refine ⟨⟨D, hD, hξ⟩, ⟨D, hD, hξ, ?_⟩, ha, ?_⟩
  · rw [MMP.Positivity.DivisorOver.codimension_center, coheight_eq_of_closure_eq_singleton sY
      (n := 3) (mod_cast hdim) (by rw [← D.center_eq_closure_genericPoint, ← hZ, hZy])]
    decide
  · rintro ⟨S, V, j, -, -, -, -, hV1, -, -, hV, -⟩
    have hc := isCentre_unique hY.toIsVariety hV ⟨D, hD, hξ, hZ⟩
    rw [hc, hZy, topologicalKrullDim_singleton] at hV1
    exact absurd hV1 (by decide)

end MMP.Fourfold

end
