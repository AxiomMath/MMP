module

public import MMP.AlgebraicGeometry.FiberSpace.VerticalFibreDivisor
public import MMP.AlgebraicGeometry.Resolution.Blowup.VarietyProjective
public import MMP.AlgebraicGeometry.MMP.Contraction.BirationalContraction
public import MMP.AlgebraicGeometry.Singularities.DiscrepancyProperties
public import MMP.AlgebraicGeometry.Singularities.Surface.LogSurfaceGerm
public import MMP.Combinatorics.WeightedGraph.Shapes
public import MMP.AlgebraicGeometry.Singularities.DivisorOverValuationIso

/-!
# Kollár et al., *Flips and abundance*: auxiliary results

Results from [Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
used in the minimal model programme: positivity of effective divisors on curves and the
propagation of support along trivially connected divisors (§15); the realization of divisorial
valuations over a dominated point (1.6.2); exceptional divisors and the exceptional set (2.16);
and the combinatorics of log discrepancy vectors of weighted dual graphs (Chapter 3).

## References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips]
-/

open scoped WithZero

universe u w

/-!
## Effective divisors meeting a curve properly have positive degree on it

Let `X` be a variety over a field `k` and `B ≥ 0` an effective `ℚ`-Cartier `ℚ`-divisor on `X`.
If a proper irreducible curve `C ⊆ X` meets `Supp B` but is not contained in it, then the
intersection number `(B · C)` is positive: after clearing denominators, the pullback of `B` to
the normalization of `C` is a nonzero effective Cartier divisor on a smooth proper curve.

#### Main results

* `MMP.Flips.intersectionNumber_pos_of_meets_supp`: `0 < (B · C)` when `C ∩ Supp B ≠ ∅` and
  `C ⊄ Supp B`.

#### Implementation notes

A proper curve `C` is recorded by its generic point `C.point`; its points are the
specializations of `C.point`. Since `Supp B` is closed, `C ⊄ Supp B` is the condition
`C.point ∉ Supp B`, and `C ∩ Supp B ≠ ∅` is the existence of a specialization of `C.point`
lying in `Supp B`. Intersection numbers `MMP.Mori.QDivisor.intersectionNumber` are defined for
`ℚ`-Cartier `ℚ`-divisors on normal locally noetherian schemes, so `X` is taken normal.

#### References

* [Kollár et al., *Flips and abundance for algebraic threefolds*, §15][KollarFlips]
-/

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}}

open CategoryTheory AlgebraicGeometry MMP.Mori in
/-- Let `X` be a (normal) variety, `B ≥ 0` an effective `ℚ`-Cartier `ℚ`-divisor and `C` a proper
curve on `X` meeting `Supp B` but not contained in it. Then `(B · C) > 0`. -/
@[mmp "lem_fa15_effective_meets_curve_positive"]
public theorem intersectionNumber_pos_of_meets_supp (sX : X ⟶ Spec (.of k))
    (hX : Mori.IsVariety k sX) [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX]
    (B : QDivisor X) (hB : B.IsQCartier) (h0 : 0 ≤ B) (C : ProperCurve sX)
    (hmeet : ∃ x : X, C.point ⤳ x ∧ x ∈ B.supp) (hC : C.point ∉ B.supp) :
    0 < B.intersectionNumber k sX C.ι C.dim_le hB := by
  obtain ⟨hnn, hiff⟩ := MMP.Fourfold.intersectionNumber_nonneg_and_eq_zero_iff sX B hB h0 C hC
  obtain ⟨x, hx, hxB⟩ := hmeet
  exact lt_of_le_of_ne hnn fun h => hiff.mp h.symm x hx hxB

end MMP.Flips

/-!
## A connected `L`-trivial curve meeting an `L`-trivial effective divisor lies in it

Let `X` be a normal proper variety over a field `k`, `L` a `ℚ`-Cartier `ℚ`-divisor and `B ≥ 0`
an effective `ℚ`-Cartier `ℚ`-divisor with `B · Γ = 0` for every proper irreducible curve `Γ`
with `L · Γ = 0`. If `C ⊆ X` is a connected proper curve all of whose irreducible components
`Cᵢ` satisfy `L · Cᵢ = 0`, and `C` meets `Supp B`, then `C ⊆ Supp B`: each component has
`B · Cᵢ = 0`, so a component meeting `Supp B` lies in it, and connectedness propagates this to
every component.

#### Main results

* `MMP.Flips.curveUnion_subset_supp_of_intersectionNumber_eq_zero`: `C ⊆ Supp B` when
  `C ∩ Supp B ≠ ∅`.

#### Implementation notes

A connected proper curve `C` is given by its irreducible components, a finite set `S` of proper
irreducible curves (`MMP.Mori.ProperCurve`), with `C = MMP.Flips.curveUnion sX S`; connectedness
is `IsConnected` of that set, which in particular makes `S` nonempty.

#### References

* [Kollár et al., *Flips and abundance for algebraic threefolds*, §15][KollarFlips]
-/

namespace MMP.Flips.Proof_lem_fa15_trivial_chain_inside_member

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Flips

/-- A preconnected set covered by finitely many closed sets, each contained in a closed set `t`
or disjoint from it, lies in `t` as soon as it meets `t`. -/
private lemma subset_of_isPreconnected_of_subset_biUnion {X ι : Type*} [TopologicalSpace X]
    {s t : Set X} {I : Finset ι} {Z : ι → Set X} (hs : IsPreconnected s) (ht : IsClosed t)
    (hZ : ∀ i ∈ I, IsClosed (Z i)) (hcov : s ⊆ ⋃ i ∈ I, Z i)
    (hdich : ∀ i ∈ I, Z i ⊆ t ∨ Disjoint (Z i) t) (hmeet : (s ∩ t).Nonempty) : s ⊆ t := by
  classical
  set D := ⋃ i ∈ I.filter (fun i => ¬ Z i ⊆ t), Z i
  have hD : IsClosed D :=
    (I.filter _).finite_toSet.isClosed_biUnion fun i hi => hZ i (Finset.mem_filter.1 hi).1
  have hcov' : s ⊆ t ∪ D := fun x hx => by
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.1 (hcov hx)
    by_cases h : Z i ⊆ t
    · exact Or.inl (h hxi)
    · exact Or.inr (Set.mem_biUnion (Finset.mem_filter.2 ⟨hi, h⟩) hxi)
  intro x hx
  refine (hcov' hx).resolve_right fun hxD => ?_
  obtain ⟨y, -, hyt, hyD⟩ := isPreconnected_closed_iff.1 hs _ _ ht hD hcov' hmeet ⟨x, hx, hxD⟩
  obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 hyD
  obtain ⟨hi, hsub⟩ := Finset.mem_filter.1 hi
  exact (hdich i hi).elim hsub fun h => h.ne_of_mem hyi hyt rfl

end MMP.Flips.Proof_lem_fa15_trivial_chain_inside_member

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}}

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Flips
  MMP.Flips.Proof_lem_fa15_trivial_chain_inside_member in
/-- Let `X` be a normal proper variety, `L` a `ℚ`-Cartier `ℚ`-divisor and `B ≥ 0` a `ℚ`-Cartier
`ℚ`-divisor with `B · Γ = 0` for every proper curve `Γ` with `L · Γ = 0`. If `C = ⋃_{Cᵢ ∈ S} Cᵢ`
is a connected proper curve with `L · Cᵢ = 0` for all its components and `C ∩ Supp B ≠ ∅`, then
`C ⊆ Supp B`. -/
@[mmp "lem_fa15_trivial_chain_inside_member"]
public theorem curveUnion_subset_supp_of_intersectionNumber_eq_zero (sX : X ⟶ Spec (.of k))
    (hX : Mori.IsVariety k sX) [IsProper sX] [IsLocallyNoetherian X] [IsNormal X]
    [QuasiCompact sX] (L : QDivisor X) (hL : L.IsQCartier) (B : QDivisor X) (hB : B.IsQCartier)
    (h0 : 0 ≤ B)
    (hBL : ∀ Γ : ProperCurve sX, L.intersectionNumber k sX Γ.ι Γ.dim_le hL = 0 →
      B.intersectionNumber k sX Γ.ι Γ.dim_le hB = 0)
    (S : Finset (ProperCurve sX)) (hconn : _root_.IsConnected (curveUnion sX S))
    (hS : ∀ C ∈ S, L.intersectionNumber k sX C.ι C.dim_le hL = 0)
    (hmeet : (curveUnion sX S ∩ (B.supp : Set X)).Nonempty) :
    curveUnion sX S ⊆ (B.supp : Set X) := by
  refine subset_of_isPreconnected_of_subset_biUnion hconn.isPreconnected B.supp.isClosed
    (fun _ _ => isClosed_closure) subset_rfl (fun C hC => ?_) hmeet
  -- A component with `L · C = 0` has `B · C = 0`, so it cannot meet `Supp B` without lying in it.
  by_cases hp : C.point ∈ (B.supp : Set X)
  · exact Or.inl (closure_minimal (Set.singleton_subset_iff.2 hp) B.supp.isClosed)
  · refine Or.inr (Set.disjoint_left.2 fun x hxC hxB => ?_)
    have := intersectionNumber_pos_of_meets_supp sX hX B hB h0 C
      ⟨x, specializes_iff_mem_closure.2 hxC, hxB⟩ hp
    exact this.ne' (hBL C (hS C hC))

end MMP.Flips

/-!
## A trivially connected prime divisor meeting an `L`-trivial effective divisor lies in it

Let `X` be a normal proper variety over a field `k` with canonical divisor `K_X`, `Δ_X` a
`ℚ`-divisor with `K_X + Δ_X` `ℚ`-Cartier, and `D` a `(K_X + Δ_X)`-trivially connected prime
divisor. Let `B ≥ 0` be an effective `ℚ`-Cartier `ℚ`-divisor with `B · Γ = 0` for every proper
irreducible curve `Γ` with `(K_X + Δ_X) · Γ = 0` (for instance `B ∼_ℚ m(K_X + Δ_X)`, `m ≥ 0`).
If `Supp B` meets `D`, then `D ⊆ Supp B`: any two points of `D` are joined inside `D` by a
connected proper curve with `(K_X + Δ_X)`-trivial components, and such a curve meeting `Supp B`
lies in it.

#### Main results

* `MMP.Flips.supp_subset_supp_of_isTriviallyConnected`: `D ⊆ Supp B` when `D ∩ Supp B ≠ ∅`.

#### Implementation notes

The prime divisor `D` is the divisor `Finsupp.single E 1` of a prime divisor `E`, and
trivial connectedness is `MMP.Flips.IsTriviallyConnected`, which carries the normality,
properness, canonicity of `K_X`, effectivity and `ℚ`-Cartierness of `K_X + Δ_X`. The proof of
`ℚ`-Cartierness used in the intersection numbers is an explicit argument `hL`; by proof
irrelevance it is the one inside `IsTriviallyConnected`.

#### References

* [Kollár et al., *Flips and abundance for algebraic threefolds*, §15][KollarFlips]
-/

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}}

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Flips in
/-- Let `X` be a normal proper variety, `K_X + Δ_X` `ℚ`-Cartier, `D` a `(K_X + Δ_X)`-trivially
connected prime divisor (`MMP.Flips.IsTriviallyConnected`), and `B ≥ 0` a `ℚ`-Cartier
`ℚ`-divisor with `B · Γ = 0` for every proper irreducible curve `Γ` with `(K_X + Δ_X) · Γ = 0`.
If `Supp B ∩ D ≠ ∅` then `D ⊆ Supp B`. -/
@[mmp "lem_fa15_trivially_connected_inside_member"]
public theorem supp_subset_supp_of_isTriviallyConnected (sX : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [QuasiCompact sX] (n : ℕ) (K : Divisor X)
    (Δ : QDivisor X) (E : Mori.PrimeDivisor X)
    (hD : IsTriviallyConnected k sX n K Δ (Finsupp.single E 1))
    (hL : (Divisor.toQDivisor K + Δ).IsQCartier) (B : QDivisor X) (hB : B.IsQCartier)
    (h0 : 0 ≤ B)
    (hBL : ∀ Γ : ProperCurve sX,
      (Divisor.toQDivisor K + Δ).intersectionNumber k sX Γ.ι Γ.dim_le hL = 0 →
        B.intersectionNumber k sX Γ.ι Γ.dim_le hB = 0)
    (hmeet : ((DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ∩
      (B.supp : Set X)).Nonempty) :
    (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ⊆ (B.supp : Set X) := by
  obtain ⟨⟨hX, _⟩, hP, -, _, -, hcon⟩ := hD
  have : IsProper sX := hP
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set Z : Set X := (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X)
  have hZ : IsClosed Z := (DivisorWithCoeffs.supp _).isClosed
  have hBc : IsClosed (B.supp : Set X) := B.supp.isClosed
  -- a closed point of `Z ∩ Supp B`
  obtain ⟨x₁, ⟨hx₁Z, hx₁B⟩, hx₁⟩ :=
    nonempty_inter_closedPoints hmeet (hZ.inter hBc).isLocallyClosed
  -- every closed point of `Z` lies in `Supp B`; in a Jacobson space that is all of `Z`
  rw [← JacobsonSpace.closure_inter_closedPoints hZ]
  refine closure_minimal (fun y ⟨hy, hyc⟩ ↦ ?_) hBc
  obtain ⟨S, hconn, -, h1, h2, hS⟩ := hcon x₁ hx₁Z y hy hx₁ hyc
  exact curveUnion_subset_supp_of_intersectionNumber_eq_zero sX hX
    (Divisor.toQDivisor K + Δ) hL B hB h0 hBL S hconn hS ⟨x₁, h1, hx₁B⟩ h2

end MMP.Flips

/-!
## A trivially connected prime divisor in a pencil-like member carries a negative curve

Let `X` be a normal proper variety over a field `k` with canonical divisor `K_X`, `Δ_X` a
`ℚ`-divisor with `L = K_X + Δ_X` `ℚ`-Cartier, and `D` an `L`-trivially connected prime divisor.
Suppose `d D + D' ∼_ℚ m L` with `d ≥ 1`, `m > 0`, `D' ≥ 0` a `ℚ`-Cartier `ℚ`-divisor, `D`
`ℚ`-Cartier, `D ⊄ Supp D'` and `D ∩ Supp D' ≠ ∅`. Then some proper irreducible curve `C ⊆ D`
has `L · C = 0` and `D · C < 0`; in particular `L + εD` is not nef for any `ε > 0`.

#### Main results

* `MMP.Flips.exists_intersectionNumber_neg_of_isTriviallyConnected`: the curve `C`.

#### Implementation notes

The prime divisor `D` is `Finsupp.single E 1` for `E : MMP.Mori.PrimeDivisor X`, and trivial
connectedness is `MMP.Flips.IsTriviallyConnected`. The condition `d D + D' ∈ |m L|` is weakened
to the `ℚ`-linear equivalence `d D + D' ∼_ℚ m L` of `ℚ`-divisors
(`MMP.Mori.QDivisor.QLinearlyEquivalent`), with `D'` a `ℚ`-divisor: an integral member of
`|m L|` gives such an equivalence, so the statement is the more general one. A curve `C ⊆ D` is
a proper curve whose generic point lies in `Supp D`.

#### References

* [Kollár et al., *Flips and abundance for algebraic threefolds*, Lemma 15.8][KollarFlips]
-/

namespace MMP.Flips.Proof_lem_fa15_trivially_connected_not_nef

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Flips

/-- If a preconnected finite union of point closures `⋃ i ∈ I, closure {p i}` meets a closed set
`t` without lying in it, then one of the points `p i` lies outside `t` while its closure meets
`t`. -/
private lemma exists_notMem_of_isPreconnected_biUnion_closure {X ι : Type*} [TopologicalSpace X]
    {t : Set X} {I : Finset ι} {p : ι → X} (hs : IsPreconnected (⋃ i ∈ I, closure {p i}))
    (ht : IsClosed t) (hmeet : ((⋃ i ∈ I, closure {p i}) ∩ t).Nonempty)
    (hnsub : ¬ (⋃ i ∈ I, closure {p i}) ⊆ t) :
    ∃ i ∈ I, p i ∉ t ∧ (closure {p i} ∩ t).Nonempty := by
  by_contra! hne
  refine hnsub
    (Proof_lem_fa15_trivial_chain_inside_member.subset_of_isPreconnected_of_subset_biUnion hs ht
      (fun _ _ => isClosed_closure)
      subset_rfl (fun i hi => ?_) hmeet)
  by_cases hp : p i ∈ t
  · exact Or.inl (closure_minimal (Set.singleton_subset_iff.2 hp) ht)
  · exact Or.inr (Set.disjoint_iff_inter_eq_empty.2 (hne i hi hp))

section Intersection

variable {k : Type u} [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
  [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX]

/-- An integral multiple of a `ℚ`-Cartier `ℚ`-divisor is `ℚ`-Cartier. -/
private lemma isQCartier_zsmul {D : QDivisor X} (hD : D.IsQCartier) (n : ℤ) :
    (n • D).IsQCartier := by
  obtain ⟨m, hm, D', hD', h⟩ := hD
  exact ⟨m, hm, n • D', by rw [map_zsmul, hD', smul_comm], h.zsmul n⟩

/-- `((n D) · C) = n (D · C)` for `n ∈ ℤ`. -/
private lemma intersectionNumber_zsmul (C : ProperCurve sX) (D : QDivisor X)
    (hD : D.IsQCartier) (n : ℤ) (hnD : (n • D).IsQCartier) :
    (n • D).intersectionNumber k sX C.ι C.dim_le hnD =
      n * D.intersectionNumber k sX C.ι C.dim_le hD := by
  have h := Fourfold.intersectionNumber_smul sX C.ι C.dim_le D hD (n : ℚ)
    (by rwa [Int.cast_smul_eq_zsmul])
  rw [← h]
  exact Fourfold.intersectionNumber_congr sX C.ι C.dim_le _ _ (Int.cast_smul_eq_zsmul ℚ n D).symm

/-- Intersection numbers with proper curves are invariant under `ℚ`-linear equivalence. -/
private lemma intersectionNumber_eq_of_qLinearlyEquivalent (C : ProperCurve sX)
    {A B : QDivisor X} (hA : A.IsQCartier) (hB : B.IsQCartier) (h : A.QLinearlyEquivalent B) :
    A.intersectionNumber k sX C.ι C.dim_le hA = B.intersectionNumber k sX C.ι C.dim_le hB := by
  obtain ⟨m, hm, φ, hφ⟩ := h
  have hdc := Divisor.isCartier_principalDivisor φ
  have hdq := QDivisor.isQCartier_toQDivisor hdc
  have hP : (Divisor.toQDivisor (principalDivisor φ)).intersectionNumber k sX C.ι C.dim_le
      hdq = 0 := by
    rw [QDivisor.intersectionNumber_toQDivisor k sX C.ι C.dim_le _ hdc hdq]
    have hiso := (Divisor.linearlyEquivalent_principalDivisor_zero φ).divisorialSheafIso
    have := hdc.isInvertibleModule_divisorialSheaf
    have := (Divisor.isCartier_zero (X := X)).isInvertibleModule_divisorialSheaf
    have h1 : (principalDivisor φ).degreeOn k sX C.ι C.dim_le hdc =
        (0 : Divisor X).degreeOn k sX C.ι C.dim_le Divisor.isCartier_zero :=
      degreeOn_eq_of_iso k sX C.ι C.dim_le hiso
    rw [h1, Divisor.degreeOn_zero' k sX C.ι C.dim_le, Int.cast_zero]
  have hmA := isQCartier_zsmul hA (m : ℤ)
  have hmB := isQCartier_zsmul hB (m : ℤ)
  have heq : (m : ℤ) • A = (m : ℤ) • B + Divisor.toQDivisor (principalDivisor φ) := by
    rw [← hφ, smul_sub, add_sub_cancel]
  have key := Fourfold.intersectionNumber_congr sX C.ι C.dim_le hmA (hmB.add hdq) heq
  rw [QDivisor.intersectionNumber_add' k sX C.ι C.dim_le _ _ hmB hdq, hP, add_zero,
    intersectionNumber_zsmul sX C A hA _ hmA, intersectionNumber_zsmul sX C B hB _ hmB] at key
  have hm' : ((m : ℤ) : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  exact mul_left_cancel₀ hm' key

end Intersection

end MMP.Flips.Proof_lem_fa15_trivially_connected_not_nef

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry

open MMP.Mori

variable {k : Type u} [Field k] {X : Scheme.{u}}

open CategoryTheory AlgebraicGeometry MMP MMP.Mori MMP.Flips
  MMP.Flips.Proof_lem_fa15_trivially_connected_not_nef in
/-- Let `X` be a normal proper variety, `L = K_X + Δ_X` `ℚ`-Cartier, `D` an `L`-trivially
connected prime divisor (`MMP.Flips.IsTriviallyConnected`), and `d D + D' ∼_ℚ m L` with `d ≥ 1`,
`m > 0`, `D' ≥ 0`, `D` and `D'` `ℚ`-Cartier, `D ⊄ Supp D'` and `D ∩ Supp D' ≠ ∅`. Then there is
a proper irreducible curve `C ⊆ D` with `L · C = 0` and `D · C < 0`. -/
@[mmp "lem_fa15_trivially_connected_not_nef"]
public theorem exists_intersectionNumber_neg_of_isTriviallyConnected (sX : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] [IsNormal X] [CompactSpace X] [QuasiCompact sX] (n : ℕ)
    (K : Divisor X) (Δ : QDivisor X) (E : Mori.PrimeDivisor X)
    (hD : IsTriviallyConnected k sX n K Δ (Finsupp.single E 1))
    (hL : (Divisor.toQDivisor K + Δ).IsQCartier)
    (hDq : (Divisor.toQDivisor (Finsupp.single E 1 : Divisor X)).IsQCartier)
    (D' : QDivisor X) (hD' : D'.IsQCartier) (h0 : 0 ≤ D') (d m : ℕ) (hd : 1 ≤ d) (hm : 0 < m)
    (hdm : ((d : ℤ) • Divisor.toQDivisor (Finsupp.single E 1 : Divisor X) + D').QLinearlyEquivalent
      ((m : ℤ) • (Divisor.toQDivisor K + Δ)))
    (hnsub : ¬ (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ⊆
      (D'.supp : Set X))
    (hmeet : ((DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ∩
      (D'.supp : Set X)).Nonempty) :
    ∃ C : ProperCurve sX,
      C.point ∈ (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X) ∧
      (Divisor.toQDivisor K + Δ).intersectionNumber k sX C.ι C.dim_le hL = 0 ∧
      (Divisor.toQDivisor (Finsupp.single E 1 : Divisor X)).intersectionNumber k sX C.ι
        C.dim_le hDq < 0 := by
  obtain ⟨⟨hX, _⟩, hP, -, _, -, hcon⟩ := hD
  have : IsProper sX := hP
  have : JacobsonSpace X := LocallyOfFiniteType.jacobsonSpace sX
  set Z : Set X := (DivisorWithCoeffs.supp (Finsupp.single E 1 : Divisor X) : Set X)
  set T : Set X := (D'.supp : Set X)
  have hZ : IsClosed Z := (DivisorWithCoeffs.supp _).isClosed
  have hT : IsClosed T := D'.supp.isClosed
  -- closed points `x₁ ∈ Z ∩ T` and `x₂ ∈ Z \ T`
  obtain ⟨x₁, ⟨hx₁Z, hx₁T⟩, hx₁⟩ :=
    nonempty_inter_closedPoints hmeet (hZ.inter hT).isLocallyClosed
  have h2 : (Z \ T).Nonempty := Set.diff_nonempty.2 hnsub
  obtain ⟨x₂, ⟨hx₂Z, hx₂T⟩, hx₂⟩ :=
    nonempty_inter_closedPoints h2 (hZ.isLocallyClosed.inter hT.isOpen_compl.isLocallyClosed)
  obtain ⟨S, hconn, hSZ, h1S, h2S, hS⟩ := hcon x₁ hx₁Z x₂ hx₂Z hx₁ hx₂
  obtain ⟨C, hCS, hCT, x, hxC, hxT⟩ := exists_notMem_of_isPreconnected_biUnion_closure
    hconn.isPreconnected hT ⟨x₁, h1S, hx₁T⟩ fun h => hx₂T (h h2S)
  have hLC := hS C hCS
  have hpos := intersectionNumber_pos_of_meets_supp sX hX D' hD' h0 C
    ⟨x, specializes_iff_mem_closure.2 hxC, hxT⟩ hCT
  refine ⟨C, hSZ (Set.mem_biUnion hCS (subset_closure rfl)), hLC, ?_⟩
  have hdD := isQCartier_zsmul hDq (d : ℤ)
  have hmL := isQCartier_zsmul hL (m : ℤ)
  have key := intersectionNumber_eq_of_qLinearlyEquivalent sX C (hdD.add hD') hmL hdm
  rw [QDivisor.intersectionNumber_add' k sX C.ι C.dim_le _ _ hdD hD',
    intersectionNumber_zsmul sX C _ hDq _ hdD, intersectionNumber_zsmul sX C _ hL _ hmL,
    hLC, mul_zero] at key
  have hd' : (1 : ℚ) ≤ ((d : ℤ) : ℚ) := by exact_mod_cast hd
  nlinarith

end MMP.Flips

/-!
## Divisors of the function field realized over a dominated point

Let `X` be a variety over a field `k`, `v` a divisor of the function field `k(X)` and `x ∈ X` a
point whose local ring `𝒪_{X,x}` is dominated by the valuation ring `𝒪_v`: every element of
`𝒪_{X,x}` has `v ≤ 1` and every element of its maximal ideal has `v < 1`. Then `v` is the
valuation `ord_F` of a divisor `(Z, h, F)` over `X` with `h(η_F) = x`, and `h` can be taken
projective. The divisor is obtained by blowing up `X` in an ideal making the generators of a
chart of a model of `v` regular, and normalizing.

#### Main results

* `MMP.Flips.exists_properDivisorOver_isProjective_of_dominates`.
* `MMP.Flips.exists_properDivisorOver_isProjective_of_dominates_of_essFiniteType`: the same for
  any `ℤᵐ⁰`-valued valuation `v` of `k(X)` taking the value `exp (-1)` whose valuation ring is the
  image of a `k`-algebra essentially of finite type; these are the only properties of a divisor
  the construction uses.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (1.6.2)
-/

namespace MMP.Flips.Proof_lem_fa1a_valuation_realized_at_dominated_point

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips

/-- A local ring of an integral scheme `Y` birational to `X` which, inside the function field, is
the valuation ring of a valuation of `k(X)` is a valuation ring. -/
private theorem valuationRing_stalk_of_forall_le_one_iff {X Y : Scheme.{w}}
    [IsIntegral X] [IsIntegral Y] (β : Y ⟶ X) (hβ : IsBirationalMorphism β)
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation X.functionField Γ) (q : Y)
    (hq : haveI : IsDominant β := hβ.isDominant
      ∀ g : X.functionField, v g ≤ 1 ↔
        ∃ a : Y.presheaf.stalk q, algebraMap _ Y.functionField a = functionFieldMap β g) :
    ValuationRing (Y.presheaf.stalk q) := by
  haveI : IsDominant β := hβ.isDominant
  let φ := RingEquiv.ofBijective (functionFieldMap β) hβ.functionFieldMap_bijective
  let w : Valuation Y.functionField Γ := v.comap φ.symm.toRingHom
  have hw : ∀ r, w r ≤ 1 ↔ ∃ a : Y.presheaf.stalk q, algebraMap _ Y.functionField a = r := by
    intro r
    have := hq (φ.symm r)
    rwa [show functionFieldMap β (φ.symm r) = φ (φ.symm r) from rfl,
      RingEquiv.apply_symm_apply] at this
  exact ValuationRing.of_integers w
    ⟨IsFractionRing.injective _ _, fun a => (hw _).2 ⟨a, rfl⟩, fun r hr => (hw r).1 hr⟩

/-- A dominant morphism of integral schemes inducing a surjection of function fields is an
isomorphism on the local ring at every point whose image has a valuation ring as local ring. -/
private theorem isIso_stalkMap_of_valuationRing {Y Z : Scheme.{w}} [IsIntegral Y] [IsIntegral Z]
    (ν : Z ⟶ Y) [IsDominant ν] (hν : Function.Surjective (functionFieldMap ν)) (z : Z)
    [ValuationRing (Y.presheaf.stalk (ν z))] : IsIso (ν.stalkMap z) := by
  set φ := (ν.stalkMap z).hom
  have hsq : ∀ a, algebraMap _ Z.functionField (φ a) =
      functionFieldMap ν (algebraMap _ Y.functionField a) := fun a =>
    (MMP.Mori.functionFieldMap_algebraMap_stalk ν z a).symm
  have hinj : Function.Injective φ := by
    intro a b hab
    apply IsFractionRing.injective (Y.presheaf.stalk (ν z)) Y.functionField
    apply (functionFieldMap ν).injective
    rw [← hsq, ← hsq, hab]
  have hsurj : Function.Surjective φ := by
    intro b
    obtain ⟨r, hr⟩ := hν (algebraMap _ Z.functionField b)
    by_cases hr0 : r = 0
    · refine ⟨0, IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField ?_⟩
      rw [map_zero, map_zero, ← hr, hr0, map_zero]
    rcases ValuationRing.isInteger_or_isInteger (Y.presheaf.stalk (ν z)) r with ⟨a, ha⟩ | ⟨c, hc⟩
    · refine ⟨a, IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField ?_⟩
      rw [hsq, ha, hr]
    · have h1 : φ c * b = 1 := by
        apply IsFractionRing.injective (Z.presheaf.stalk z) Z.functionField
        rw [map_mul, hsq, hc, ← hr, ← map_mul, inv_mul_cancel₀ hr0, map_one, map_one]
      have hcu : IsUnit c := (isUnit_map_iff φ c).mp (IsUnit.of_mul_eq_one _ h1)
      obtain ⟨d, hd⟩ := hcu.exists_left_inv
      refine ⟨d, ?_⟩
      calc φ d = φ d * (φ c * b) := by rw [h1, mul_one]
        _ = b := by rw [← mul_assoc, ← map_mul, hd, map_one, one_mul]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

/-- A morphism of integral schemes, locally of finite type and birational in the sense of
`AlgebraicGeometry.IsBirational`, is a birational morphism. -/
private theorem isBirationalMorphism_of_isBirational {X Y : Scheme.{w}} [IsIntegral X]
    [IsIntegral Y] (f : X ⟶ Y) [LocallyOfFiniteType f] (hf : IsBirational f) :
    IsBirationalMorphism f := by
  haveI : Finite (irreducibleComponents X) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  haveI : Finite (irreducibleComponents Y) := by
    rw [irreducibleComponents_eq_singleton]
    exact Set.finite_singleton _
  obtain ⟨U, V, hUV, hU, hV, hiso⟩ :=
    exists_dense_opens_isIso_resLE_of_isBirational f hf (Or.inl ⟨inferInstance, inferInstance⟩)
  exact isBirationalMorphism_of_isIso_resLE f U V hU.nonempty hV.nonempty hUV hiso

/-- An ideal of the sections over an affine open extends to an ideal sheaf: the kernel of the
closed subscheme `Spec (Γ(X, U) ⧸ J) ⟶ X`, i.e. the ideal sheaf of its scheme-theoretic closure. -/
private theorem exists_idealSheafData_ideal_eq {X : Scheme.{w}} [QuasiSeparatedSpace X]
    (U : X.affineOpens) (J : Ideal Γ(X, U)) : ∃ ℐ : X.IdealSheafData, ℐ.ideal U = J := by
  have hU : IsAffineOpen (U : X.Opens) := U.2
  let φ := CommRingCat.ofHom (Ideal.Quotient.mk J)
  let π : Spec (.of (Γ(X, U) ⧸ J)) ⟶ X := Spec.map φ ≫ hU.fromSpec
  refine ⟨π.ker, ?_⟩
  rw [Scheme.Hom.ker_apply]
  ext a
  rw [RingHom.mem_ker]
  have hle : (⊤ : (Spec (.of (Γ(X, U) ⧸ J))).Opens) ≤ π ⁻¹ᵁ U := by
    intro y _
    change hU.fromSpec ((Spec.map φ) y) ∈ (U : X.Opens)
    exact hU.range_fromSpec.subset ⟨_, rfl⟩
  have hres : (π.app U).hom a = 0 ↔ (π.appLE U ⊤ hle).hom a = 0 := by
    have heq : (homOfLE hle) = eqToHom (top_le_iff.mp hle).symm := Subsingleton.elim _ _
    rw [Scheme.Hom.appLE, heq, CommRingCat.comp_apply]
    exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
      ((Spec (.of (Γ(X, U) ⧸ J))).presheaf.map (eqToHom (top_le_iff.mp hle).symm).op)).1).symm
  have hcomp : π.appLE U ⊤ hle = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map φ).appTop := by
    rw [Scheme.Hom.comp_appLE, hU.fromSpec_app_self, Category.assoc]
    congr 1
  rw [hres, hcomp, CommRingCat.comp_apply]
  have hnat := congrArg (fun g => g.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom a))
    (Scheme.ΓSpecIso_naturality φ)
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply] at hnat
  rw [← map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ J))).hom).1]
  erw [hnat]
  rw [CommRingCat.comp_apply]
  erw [Iso.inv_hom_id_apply]
  exact Ideal.Quotient.eq_zero_iff_mem (I := J)

/-- A unit of a ring mapping into the valuation ring of `w` maps to an element of value `1`. -/
private theorem valuation_eq_one_of_isUnit {S L : Type*} [CommRing S] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (φ : S →+* L)
    (hφ : ∀ s, w (φ s) ≤ 1) {t : S} (ht : IsUnit t) : w (φ t) = 1 := by
  obtain ⟨u, rfl⟩ := ht
  refine le_antisymm (hφ _) ?_
  by_contra hlt
  push Not at hlt
  have h1 : w (φ u) * w (φ ↑u⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  have h2 : w (φ u) * w (φ ↑u⁻¹) < 1 := mul_lt_one_of_lt_of_le hlt (hφ _)
  exact (ne_of_lt h2) h1

/-- Let `φ : S → L` land in the valuation ring of `w`, with `S` essentially of finite type over
`R`. If a subring `C` contains the images of `R` and of the generators of `S`, every `φ s` is a
fraction `c / t` with `c, t ∈ C` and `w t = 1`. -/
private theorem exists_mul_eq_of_essFiniteType {R S L : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.EssFiniteType R S] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (φ : S →+* L)
    (hφ : ∀ s, w (φ s) ≤ 1) (C : Subring L) (hR : ∀ r, φ (algebraMap R S r) ∈ C)
    (hσ : ∀ s ∈ Algebra.EssFiniteType.finset R S, φ s ∈ C) (s : S) :
    ∃ c ∈ C, ∃ t ∈ C, w t = 1 ∧ φ s * t = c := by
  have hcond := (Algebra.essFiniteType_cond_iff R S (Algebra.EssFiniteType.finset R S)).mp
    (Algebra.EssFiniteType.isLocalization R S)
  have hadj : ∀ y ∈ Algebra.adjoin R (Algebra.EssFiniteType.finset R S : Set S), φ y ∈ C := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hσ x hx
    | algebraMap r => exact hR r
    | add x y _ _ hx hy => rw [map_add]; exact C.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact C.mul_mem hx hy
  obtain ⟨t, ht, htu, hst⟩ := hcond s
  exact ⟨φ (s * t), hadj _ hst, φ t, hadj _ ht, valuation_eq_one_of_isUnit w φ hφ htu,
    (map_mul φ s t).symm⟩

/-- If every element of `J` has value at most that of `h`, every element of `Jⁿ` has value at
most that of `hⁿ`. -/
private theorem valuation_le_pow_of_mem_pow {A L : Type*} [CommRing A] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (ι : A →+* L)
    (hA : ∀ a, w (ι a) ≤ 1) (J : Ideal A) (h : A) (hJ : ∀ y ∈ J, w (ι y) ≤ w (ι h)) :
    ∀ n : ℕ, ∀ y ∈ J ^ n, w (ι y) ≤ w (ι h) ^ n := by
  intro n
  induction n with
  | zero => intro y _; rw [pow_zero]; exact hA y
  | succ n ih =>
    intro y hy
    rw [pow_succ] at hy
    refine Submodule.mul_induction_on hy (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [map_mul, map_mul, pow_succ]
      exact mul_le_mul' (ih a ha) (hJ b hb)
    · rw [map_add]
      exact (w.map_add _ _).trans (max_le ha hb)

/-- The local rings of a scheme locally of finite type over a field `k` are essentially of
finite type over `k`. -/
private theorem essFiniteType_stalkAlgebra {k : Type w} [Field k] {Y : Scheme.{w}}
    (sY : Y ⟶ Spec (.of k)) [LocallyOfFiniteType sY] (y : Y) :
    letI := stalkAlgebra sY y
    Algebra.EssFiniteType k (Y.presheaf.stalk y) := by
  letI := stalkAlgebra sY y
  have := (sY.base y).isPrime
  have h0 : (algebraMap k (Localization.AtPrime (sY.base y).asIdeal)).EssFiniteType := by
    rw [RingHom.essFiniteType_algebraMap]
    exact Algebra.EssFiniteType.of_isLocalization _ (sY.base y).asIdeal.primeCompl
  have hiso : (Spec.stalkIso (.of k) (sY.base y)).inv.hom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _
      (asIso (Spec.stalkIso (.of k) (sY.base y)).inv).commRingCatIsoToRingEquiv.surjective
      ).essFiniteType
  have h1 : ((Scheme.ΓSpecIso (.of k)).inv ≫
      (Spec (.of k)).presheaf.germ ⊤ (sY.base y) (by simp)).hom.EssFiniteType := by
    have e := congrArg CommRingCat.Hom.hom
      (Spec.algebraMap_stalkIso_inv (R := .of k) (x := sY.base y))
    rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom] at e
    rw [← e]
    exact h0.comp hiso
  have h2 := h1.comp (LocallyOfFiniteType.stalkMap sY y)
  rw [← RingHom.essFiniteType_algebraMap]
  convert h2 using 1
  change ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.presheaf.germ ⊤ y (by simp)).hom = _
  rw [← CommRingCat.hom_comp, Category.assoc, Scheme.Hom.germ_stalkMap]
  rfl

/-- The valuation ring of a divisor of the function field, as the image of a `k`-algebra
essentially of finite type. -/
private theorem IsDivisorOfFunctionField.exists_essFiniteType {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] {v : Valuation X.functionField ℤᵐ⁰}
    (hv : IsDivisorOfFunctionField k sX v) :
    letI := functionFieldAlgebra sX
    ∃ (S : Type w) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
      (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range := by
  letI := functionFieldAlgebra sX
  obtain ⟨Y, sY, hY, E, hE⟩ := hv
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : LocallyOfFiniteType sY := hY.1.toLocallyOfFiniteType
  haveI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian sY
  letI := functionFieldAlgebra sY
  obtain ⟨e, rfl⟩ := hE
  letI := stalkAlgebra sY E.genericPoint
  haveI := essFiniteType_stalkAlgebra sY E.genericPoint
  haveI := isScalarTower_stalk_functionField sY E.genericPoint
  refine ⟨Y.presheaf.stalk E.genericPoint, inferInstance, inferInstance, inferInstance,
    (e.symm : Y.functionField →ₐ[k] X.functionField).comp
      (IsScalarTower.toAlgHom k _ Y.functionField), fun g => ?_⟩
  rw [Valuation.comap_apply, PrimeDivisor.divisorialValuation_le_one_iff]
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨s, ?_⟩
    change e.symm (algebraMap (Y.presheaf.stalk E.genericPoint) Y.functionField s) = g
    erw [hs]
    exact e.symm_apply_apply g
  · rintro ⟨s, rfl⟩
    refine ⟨s, ?_⟩
    change _ = e (e.symm (algebraMap (Y.presheaf.stalk E.genericPoint) Y.functionField s))
    rw [AlgEquiv.apply_symm_apply]

/-- Sections pulled back along a dominant morphism of integral schemes map to the function field
through `functionFieldMap`. -/
private theorem germToFunctionField_appLE {X Y : Scheme.{w}} [IsIntegral X] [IsIntegral Y]
    (f : Y ⟶ X) [IsDominant f] (U : X.Opens) (V : Y.Opens) [Nonempty U] [Nonempty V]
    (h : V ≤ f ⁻¹ᵁ U) (s : Γ(X, U)) :
    Y.germToFunctionField V (f.appLE U V h s) = functionFieldMap f (X.germToFunctionField U s) := by
  obtain ⟨⟨y, hy⟩⟩ := ‹Nonempty V›
  rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := Y) hy,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (h hy),
    MMP.Mori.functionFieldMap_algebraMap_stalk]
  congr 1
  erw [Scheme.Hom.germ_stalkMap_apply]
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]

/-- The constants `k ⊆ k(X)` are sections over every nonempty open. -/
private theorem exists_germToFunctionField_eq_algebraMap {k : Type w} [Field k] {X : Scheme.{w}}
    (sX : X ⟶ Spec (.of k)) [IsIntegral X] (U : X.Opens) [Nonempty U] (c : k) :
    letI := functionFieldAlgebra sX
    ∃ a : Γ(X, U), X.germToFunctionField U a = algebraMap k X.functionField c := by
  letI := functionFieldAlgebra sX
  refine ⟨X.presheaf.map (homOfLE le_top).op (sX.appTop ((Scheme.ΓSpecIso (.of k)).inv c)), ?_⟩
  change X.presheaf.germ U _ _ _ = ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫
    X.presheaf.germ ⊤ (genericPoint X) (by simp)) c
  rw [TopCat.Presheaf.germ_res_apply]
  rfl

/-- The prime of the point of an affine open given by a prime `P` of its sections is `P`. -/
private theorem primeIdealOf_fromSpec {X : Scheme.{w}} {W : X.Opens} (hW : IsAffineOpen W)
    (P : PrimeSpectrum Γ(X, W)) (hP : hW.fromSpec P ∈ W) :
    hW.primeIdealOf ⟨hW.fromSpec P, hP⟩ = P := by
  have : (⟨hW.fromSpec P, hP⟩ : W) = hW.isoSpec.inv P := rfl
  rw [this]
  have h := Scheme.Hom.comp_apply hW.isoSpec.inv hW.isoSpec.hom (show Spec Γ(X, W) from P)
  rw [Iso.inv_hom_id] at h
  exact h.symm

/-- If every generator of an ideal has value at most `b`, so does every element. -/
private theorem valuation_le_of_mem_span {A L : Type*} [CommRing A] [Field L] {Γ : Type*}
    [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (ι : A →+* L)
    (hA : ∀ a, w (ι a) ≤ 1) {s : Set A} {b : Γ} (hs : ∀ z ∈ s, w (ι z) ≤ b) :
    ∀ y ∈ Ideal.span s, w (ι y) ≤ b := by
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz => exact hs z hz
  | zero => rw [map_zero, map_zero]; exact zero_le'
  | add y z _ _ hy hz => rw [map_add]; exact (w.map_add _ _).trans (max_le hy hz)
  | smul c y _ hy =>
    rw [smul_eq_mul, map_mul, map_mul]
    exact (mul_le_of_le_one_left' (hA c)).trans hy

/-- If `t * χ h ^ n = χ y` with `y ∈ Jⁿ`, where every element of `J` has value at most that of
`h ≠ 0`, then `t` has value at most `1`. -/
private theorem valuation_le_one_of_mul_pow_eq {A B K L : Type*} [CommRing A] [CommRing B]
    [Field K] [Field L] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
    (w : Valuation L Γ) (ι : A →+* K) (χ : A →+* B) (ψ : B →+* L) (hA : ∀ a, v (ι a) ≤ 1)
    (J : Ideal A) (h : A) (hJ : ∀ y ∈ J, v (ι y) ≤ v (ι h)) (hh : ι h ≠ 0)
    (hwv : ∀ s, w (ψ (χ s)) = v (ι s)) {t : B} {n : ℕ} {y : A} (hy : y ∈ J ^ n)
    (hty : t * χ h ^ n = χ y) : w (ψ t) ≤ 1 := by
  have h3 := valuation_le_pow_of_mem_pow v ι hA J h hJ n y hy
  have h2 : w (ψ t) * v (ι h) ^ n = v (ι y) := by
    rw [← hwv, ← hwv, ← hty]
    simp only [map_mul, map_pow]
  rw [← h2] at h3
  have hpos : 0 < v (ι h) ^ n := pow_pos (zero_lt_iff.mpr fun h0 => hh ((v.zero_iff).mp h0)) n
  exact (mul_le_iff_le_one_left hpos).mp h3

/-- For a ring map `ψ : A → L` landing in the valuation ring of `w`, the elements of `A` of value
`< 1` form a prime ideal. -/
private theorem exists_isPrime_forall_mem_iff_lt_one {A L : Type*} [CommRing A] [Field L]
    {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] (w : Valuation L Γ) (ψ : A →+* L)
    (hA : ∀ a, w (ψ a) ≤ 1) : ∃ 𝔮 : Ideal A, 𝔮.IsPrime ∧ ∀ t, t ∈ 𝔮 ↔ w (ψ t) < 1 := by
  let 𝔮 : Ideal A :=
    { carrier := {t | w (ψ t) < 1}
      add_mem' := fun {y z} hy hz => by
        simp only [Set.mem_setOf_eq, map_add] at *
        exact (w.map_add _ _).trans_lt (max_lt hy hz)
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        simp only [Set.mem_setOf_eq, smul_eq_mul, map_mul] at *
        exact (mul_le_of_le_one_left' (hA c)).trans_lt hy }
  have h𝔮 : ∀ t, t ∈ 𝔮 ↔ w (ψ t) < 1 := fun _ => Iff.rfl
  refine ⟨𝔮, ⟨?_, fun {y z} h => ?_⟩, h𝔮⟩
  · rw [Ideal.ne_top_iff_one, h𝔮, map_one, map_one]
    exact lt_irrefl _
  · rw [h𝔮, map_mul, map_mul] at h
    rw [h𝔮, h𝔮]
    by_contra hc
    push Not at hc
    rw [le_antisymm (hA y) hc.1, le_antisymm (hA z) hc.2, one_mul] at h
    exact lt_irrefl _ h

/-- The chart of the blow-up at a nonzero section over an integral affine open is nonempty. -/
private theorem nonempty_blowUpChartOpen {X : Scheme.{w}} (ℐ : X.IdealSheafData)
    [IsIntegral X] (U : X.affineOpens) [Nonempty U.1] (a : ℐ.ideal U) (ha : (a : Γ(X, U.1)) ≠ 0) :
    Nonempty (blowUpChartOpen ℐ U a).1 := by
  have hW : IsAffineOpen (blowUpChartOpen ℐ U a).1 := (blowUpChartOpen ℐ U a).2
  haveI : Nontrivial Γ(blowUp ℐ, (blowUpChartOpen ℐ U a).1) := by
    haveI : Nontrivial (Localization.Away (a : Γ(X, U.1))) := by
      have hinj := IsLocalization.injective (Localization.Away (a : Γ(X, U.1)))
        (powers_le_nonZeroDivisors_of_noZeroDivisors ha)
      exact ⟨⟨_, _, hinj.ne zero_ne_one⟩⟩
    exact (blowUpChartRingIso ℐ U a).commRingCatIsoToRingEquiv.toEquiv.nontrivial
  obtain ⟨p₀, hp₀⟩ := Ideal.exists_maximal Γ(blowUp ℐ, (blowUpChartOpen ℐ U a).1)
  exact ⟨⟨hW.fromSpec (show Spec _ from ⟨p₀, hp₀.isPrime⟩), hW.range_fromSpec.subset ⟨_, rfl⟩⟩⟩

/-- Let `f` map an affine open `W` into an affine open `U`. The point of `W` given by a prime `P`
of its sections lies over `x ∈ U` if `P` pulls back to the prime of `x`. -/
private theorem apply_fromSpec_eq_of_forall_mem_iff {X Y : Scheme.{w}} (f : Y ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) {W : Y.Opens} (hW : IsAffineOpen W)
    (hWle : W ≤ f ⁻¹ᵁ U) (P : PrimeSpectrum Γ(Y, W)) (hPW : hW.fromSpec P ∈ W) {x : X}
    (hxU : x ∈ U)
    (h : ∀ s, (f.appLE U W hWle).hom s ∈ P.asIdeal ↔ s ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) :
    f (hW.fromSpec P) = x := by
  have h2 : hU.primeIdealOf ⟨f (hW.fromSpec P), hWle hPW⟩ = hU.primeIdealOf ⟨x, hxU⟩ := by
    rw [← IsAffineOpen.comap_primeIdealOf_appLE U hU W hW hWle hPW, primeIdealOf_fromSpec hW P hPW]
    exact PrimeSpectrum.ext (Ideal.ext h)
  have := congrArg hU.fromSpec h2
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at this

/-- Let `P` be the prime of the sections over a nonempty affine open `W` of an integral scheme of
`w`-value `< 1`, all sections having value `≤ 1`. If every element of the valuation ring of `w` is
a fraction `c / t` of sections with `w t = 1`, that valuation ring is the local ring at `P`. -/
private theorem valuation_le_one_iff_exists_stalk {Y : Scheme.{w}} [IsIntegral Y] {W : Y.Opens}
    (hW : IsAffineOpen W) [Nonempty W] {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]
    (w : Valuation Y.functionField Γ) (hle : ∀ t, w ((Y.germToFunctionField W).hom t) ≤ 1)
    (P : PrimeSpectrum Γ(Y, W))
    (hP : ∀ t, t ∈ P.asIdeal ↔ w ((Y.germToFunctionField W).hom t) < 1)
    (hPW : hW.fromSpec P ∈ W)
    (hfrac : ∀ g, w g ≤ 1 → ∃ c t, w ((Y.germToFunctionField W).hom t) = 1 ∧
      g * (Y.germToFunctionField W).hom t = (Y.germToFunctionField W).hom c) (g) :
    w g ≤ 1 ↔ ∃ a : Y.presheaf.stalk (hW.fromSpec P), algebraMap _ Y.functionField a = g := by
  set ψ := (Y.germToFunctionField W).hom
  letI : Algebra Γ(Y, W) (Y.presheaf.stalk (hW.fromSpec P)) :=
    TopCat.Presheaf.algebra_section_stalk _ ⟨_, hPW⟩
  haveI : IsLocalization P.asIdeal.primeCompl (Y.presheaf.stalk (hW.fromSpec P)) :=
    hW.isLocalization_stalk' P hPW
  haveI := functionField_isScalarTower Y W ⟨_, hPW⟩
  have hμ : ∀ t, algebraMap _ Y.functionField (algebraMap Γ(Y, W)
      (Y.presheaf.stalk (hW.fromSpec P)) t) = ψ t := fun t => by
    rw [← IsScalarTower.algebraMap_apply]; rfl
  have hmk : ∀ c (t : P.asIdeal.primeCompl), algebraMap _ Y.functionField
      (IsLocalization.mk' (Y.presheaf.stalk (hW.fromSpec P)) c t) * ψ t = ψ c :=
    fun c t => by rw [← hμ, ← hμ, ← map_mul, IsLocalization.mk'_spec]
  constructor
  · intro hg
    obtain ⟨c, t, ht, hct⟩ := hfrac g hg
    have htq : t ∈ P.asIdeal.primeCompl := fun h => ((hP t).1 h).ne ht
    refine ⟨IsLocalization.mk' _ c ⟨t, htq⟩, ?_⟩
    have hψt : ψ t ≠ 0 := fun h => by simp [h] at ht
    exact mul_right_cancel₀ hψt ((hmk c ⟨t, htq⟩).trans hct.symm)
  · rintro ⟨y, rfl⟩
    obtain ⟨⟨c, t⟩, rfl⟩ := IsLocalization.mk'_surjective P.asIdeal.primeCompl y
    have ht1 : w (ψ t) = 1 := le_antisymm (hle t) (not_lt.mp fun h => t.2 ((hP t).2 h))
    have h := congrArg w (hmk c t)
    rw [map_mul, ht1, mul_one] at h
    exact h.trans_le (hle c)

/-- **The blow-up of an ideal on a chart.** Let `J ∋ h₀ ≠ 0` be an ideal of the sections over an
affine open `U ∋ x` such that `J` has values at most `v h₀` and contains `h₀ φ(s)` for the
generators `s` of an algebra `S` whose image is the valuation ring of `v`. On the blow-up of an
ideal sheaf restricting to `J`, the point of the chart `Spec Γ(X, U)[J/h₀]` cut out by `𝔪_v` lies
over `x` and has the valuation ring of `v` as local ring. -/
private theorem exists_blowUp_stalk_eq_integer_of_ideal_eq {X : Scheme.{w}} [IsIntegral X]
    {v : Valuation X.functionField ℤᵐ⁰} {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (f : S →+* X.functionField) (hf : ∀ g, v g ≤ 1 ↔ ∃ s, f s = g)
    {U : X.Opens} (hU : IsAffineOpen U) [Nonempty U] {x : X} (hxU : x ∈ U)
    (hιle : ∀ a, v ((X.germToFunctionField U).hom a) ≤ 1)
    (hιlt : ∀ a, a ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ↔
      v ((X.germToFunctionField U).hom a) < 1)
    (hR : ∀ r, ∃ c, (X.germToFunctionField U).hom c = f (algebraMap R S r))
    {J : Ideal Γ(X, U)} {h₀ : Γ(X, U)} (hh₀J : h₀ ∈ J) (hh₀ : h₀ ≠ 0)
    (hJ : ∀ y ∈ J, v ((X.germToFunctionField U).hom y) ≤ v ((X.germToFunctionField U).hom h₀))
    (hσ : ∀ s ∈ Algebra.EssFiniteType.finset R S, ∃ y ∈ J,
      (X.germToFunctionField U).hom y = (X.germToFunctionField U).hom h₀ * f s)
    (ℐ : X.IdealSheafData) (hℐ : ℐ.ideal ⟨U, hU⟩ = J) [IsIntegral (blowUp ℐ)]
    [IsDominant (blowUpToBase ℐ)]
    (hsurj : Function.Surjective (functionFieldMap (blowUpToBase ℐ))) :
    ∃ q : blowUp ℐ, blowUpToBase ℐ q = x ∧
      ∀ g : X.functionField, v g ≤ 1 ↔ ∃ a : (blowUp ℐ).presheaf.stalk q,
        algebraMap _ (blowUp ℐ).functionField a = functionFieldMap (blowUpToBase ℐ) g := by
  set ι := (X.germToFunctionField U).hom
  have hιh₀ : ι h₀ ≠ 0 := (map_ne_zero_iff ι (X.germToFunctionField_injective U)).mpr hh₀
  let U' : X.affineOpens := ⟨U, hU⟩
  have hmemJ : ∀ y ∈ J, y ∈ ℐ.ideal U' := fun y hy => by rwa [hℐ]
  let a : ℐ.ideal U' := ⟨h₀, hmemJ _ hh₀J⟩
  let W := blowUpChartOpen ℐ U' a
  have hW : IsAffineOpen W.1 := W.2
  have hWle : W.1 ≤ blowUpToBase ℐ ⁻¹ᵁ U := blowUpChartOpen_le ℐ U' a
  let χ : Γ(X, U) →+* Γ(blowUp ℐ, W.1) := (blowUpChartMap ℐ U' a).hom
  haveI : Nonempty W.1 := nonempty_blowUpChartOpen ℐ U' a hh₀
  let ψ : Γ(blowUp ℐ, W.1) →+* (blowUp ℐ).functionField :=
    ((blowUp ℐ).germToFunctionField W.1).hom
  set fβ := functionFieldMap (blowUpToBase ℐ)
  have hψχ : ∀ s, ψ (χ s) = fβ (ι s) := fun s =>
    germToFunctionField_appLE (blowUpToBase ℐ) U W.1 hWle s
  let e := RingEquiv.ofBijective fβ ⟨fβ.injective, hsurj⟩
  let w : Valuation (blowUp ℐ).functionField ℤᵐ⁰ := v.comap e.symm.toRingHom
  have hw : ∀ g, w (fβ g) = v g := fun g => by
    simp only [w, Valuation.comap_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe]
    exact congrArg v (e.symm_apply_apply g)
  have hTle : ∀ t, w (ψ t) ≤ 1 := fun t => by
    obtain ⟨n, y, hy, hty⟩ := exists_mem_pow_mul_eq_blowUpChartMap ℐ U' a t
    exact valuation_le_one_of_mul_pow_eq v w ι χ ψ hιle J h₀ hJ hιh₀
      (fun s => by rw [hψχ, hw]) (hℐ ▸ hy) hty
  have hfrac := exists_mul_eq_of_essFiniteType w (fβ.comp f)
    (fun s => by change w (fβ (f s)) ≤ 1; rw [hw]; exact (hf _).2 ⟨s, rfl⟩) ψ.range
    (fun r => by obtain ⟨c, hc⟩ := hR r; exact ⟨χ c, (hψχ c).trans (congrArg fβ hc)⟩)
    (fun s hs => by
      obtain ⟨y, hy, hys⟩ := hσ s hs
      obtain ⟨t, ht⟩ := exists_mul_eq_blowUpChartMap_of_mem_pow ℐ U' a (n := 1) (x := y)
        (by rw [pow_one]; exact hmemJ _ hy)
      refine ⟨t, ?_⟩
      have ht' : χ y = χ h₀ ^ 1 * t := ht
      have := congrArg ψ ht'
      rw [pow_one, map_mul, hψχ, hψχ, hys, map_mul] at this
      exact (mul_left_cancel₀ ((map_ne_zero fβ).mpr hιh₀) this).symm)
  obtain ⟨𝔮, h𝔮p, h𝔮⟩ := exists_isPrime_forall_mem_iff_lt_one w ψ hTle
  let P : PrimeSpectrum Γ(blowUp ℐ, W.1) := ⟨𝔮, h𝔮p⟩
  have hqW : hW.fromSpec P ∈ W.1 := hW.range_fromSpec.subset ⟨P, rfl⟩
  refine ⟨hW.fromSpec P, apply_fromSpec_eq_of_forall_mem_iff _ hU hW hWle P hqW hxU fun s => ?_,
    fun g' => ?_⟩
  · rw [hιlt, ← hw, ← hψχ]
    exact h𝔮 (χ s)
  rw [← hw g']
  refine valuation_le_one_iff_exists_stalk hW w hTle P h𝔮 hqW (fun g hg => ?_) _
  obtain ⟨g, rfl⟩ := hsurj g
  obtain ⟨s, rfl⟩ := (hf g).1 (by rwa [hw] at hg)
  obtain ⟨_, ⟨c, rfl⟩, _, ⟨t, rfl⟩, ht, hct⟩ := hfrac s
  exact ⟨c, t, ht, hct⟩

/-- **The chart of the blow-up.** There are an affine open `U ∋ x` and a nonzero ideal
`J = (h₀, g₁, …, gₖ)` of `Γ(X, U)` such that, on the blow-up of any ideal sheaf restricting to `J`
on `U`, the point of the chart `Spec Γ(X, U)[J/h₀]` cut out by `𝔪_v` lies over `x` and has the
valuation ring of `v` as local ring. -/
private theorem exists_affineOpen_ideal_blowUp_stalk_eq_integer {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    {v : Valuation X.functionField ℤᵐ⁰} (hS : letI := functionFieldAlgebra sX
      ∃ (S : Type w) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1) :
    ∃ (U : X.affineOpens) (J : Ideal Γ(X, U)), x ∈ (U : X.Opens) ∧ J ≠ ⊥ ∧
      ∀ (ℐ : X.IdealSheafData), ℐ.ideal U = J → ∀ [IsIntegral (blowUp ℐ)]
        [IsDominant (blowUpToBase ℐ)], Function.Surjective (functionFieldMap (blowUpToBase ℐ)) →
        ∃ q : blowUp ℐ, blowUpToBase ℐ q = x ∧
          ∀ g : X.functionField, v g ≤ 1 ↔ ∃ a : (blowUp ℐ).presheaf.stalk q,
            algebraMap _ (blowUp ℐ).functionField a = functionFieldMap (blowUpToBase ℐ) g := by
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  letI := functionFieldAlgebra sX
  obtain ⟨S, _, _, _, φ, hφ⟩ := hS
  obtain ⟨U, hU, hxU, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show x ∈ (⊤ : X.Opens) from trivial)
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  let ι : Γ(X, U) →+* X.functionField := (X.germToFunctionField U).hom
  have hι : ∀ a, algebraMap Γ(X, U) X.functionField a = ι a := fun _ => rfl
  have hιle : ∀ a, v (ι a) ≤ 1 := fun a => by
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hxU]; exact hle _
  have hιlt : ∀ a, a ∈ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal ↔ v (ι a) < 1 := by
    intro a
    rw [hU.primeIdealOf_eq_map_closedPoint]
    change X.presheaf.germ U x hxU a ∈ IsLocalRing.maximalIdeal _ ↔ _
    rw [← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) hxU]
    refine ⟨hlt _, fun h => ?_⟩
    by_contra hm
    exact h.ne (valuation_eq_one_of_isUnit v _ hle (IsLocalRing.notMem_maximalIdeal.mp hm))
  classical
  set σ := Algebra.EssFiniteType.finset k S
  obtain ⟨⟨h₀, hh₀⟩, hden⟩ :=
    IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors Γ(X, U)) (σ.image φ)
  have hden' : ∀ s ∈ σ, ∃ r : Γ(X, U), ι r = ι h₀ * φ s := fun s hs => by
    obtain ⟨r, hr⟩ := hden (φ s) (Finset.mem_image_of_mem _ hs)
    exact ⟨r, by rw [← hι, hr, Algebra.smul_def, hι]⟩
  choose! g hg using hden'
  have hh₀0 : h₀ ≠ 0 := nonZeroDivisors.ne_zero hh₀
  have hJ := valuation_le_of_mem_span v ι hιle (s := insert h₀ (g '' σ)) (b := v (ι h₀)) <| by
    rintro _ (rfl | ⟨s, hs, rfl⟩)
    · exact le_rfl
    · rw [hg s hs, map_mul]
      exact mul_le_of_le_one_right' ((hφ _).2 ⟨s, rfl⟩)
  refine ⟨⟨U, hU⟩, _, hxU, ?_, fun ℐ hℐ _ _ hsurj =>
    exists_blowUp_stalk_eq_integer_of_ideal_eq φ.toRingHom
      (fun g => (hφ g).trans (AlgHom.mem_range φ))
      hU hxU hιle hιlt (fun r => ?_) (Ideal.subset_span (Set.mem_insert _ _)) hh₀0 hJ
      (fun s hs => ⟨g s, Ideal.subset_span (Set.mem_insert_of_mem _ ⟨s, hs, rfl⟩), hg s hs⟩)
      ℐ hℐ hsurj⟩
  · rw [ne_eq, Ideal.span_eq_bot]
    push Not
    exact ⟨h₀, Set.mem_insert _ _, hh₀0⟩
  · obtain ⟨c, hc⟩ := exists_germToFunctionField_eq_algebraMap sX U r
    exact ⟨c, hc.trans (φ.commutes r).symm⟩

/-- **The blow-up step.** There is a projective birational `β : X₂ ⟶ X` from a variety and a
point `q ↦ x` of `X₂` whose local ring, inside `k(X)`, is the valuation ring of `v`. -/
private theorem exists_blowUp_stalk_eq_integer {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    {v : Valuation X.functionField ℤᵐ⁰} (hS : letI := functionFieldAlgebra sX
      ∃ (S : Type w) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1) :
    ∃ (X₂ : Scheme.{w}) (β : X₂ ⟶ X) (_ : AlgebraicGeometry.IsVariety k (β ≫ sX))
      (hβ : IsBirationalMorphism β),
      IsProjective β ∧ ∃ q : X₂, β q = x ∧
        haveI : IsDominant β := hβ.isDominant
        ∀ g : X.functionField, v g ≤ 1 ↔
          ∃ a : X₂.presheaf.stalk q, algebraMap _ X₂.functionField a = functionFieldMap β g := by
  obtain ⟨U, J, -, hJ, hchart⟩ := exists_affineOpen_ideal_blowUp_stalk_eq_integer sX hS x hle hlt
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
  obtain ⟨ℐ, hℐ⟩ := exists_idealSheafData_ideal_eq U J
  have hℐ0 : ℐ ≠ ⊥ := by
    rintro rfl
    exact hJ (hℐ.symm.trans rfl)
  obtain ⟨hvar, hproj, hbir⟩ :=
    MMP.Flips.ResolutionInputs.isVariety_blowUp_and_isProjective_and_isBirational sX ℐ hℐ0
  haveI : IsIntegral (blowUp ℐ) := hvar.toIsIntegral
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  haveI : IsProper (blowUpToBase ℐ) := hproj.isProper
  have hβ := isBirationalMorphism_of_isBirational (blowUpToBase ℐ) hbir
  haveI : IsDominant (blowUpToBase ℐ) := hβ.isDominant
  obtain ⟨q, hq, hstalk⟩ := hchart ℐ hℐ hβ.functionFieldMap_bijective.2
  exact ⟨blowUp ℐ, blowUpToBase ℐ, hvar, hβ, hproj, q, hq, hstalk⟩

/-- **The normalization step.** The normalization of a variety is a finite, hence projective,
birational morphism from a normal variety, and it is an isomorphism on local rings over a point
whose local ring is a valuation ring. -/
private theorem exists_normalization_isIso_stalkMap {k : Type w} [Field k] {Y : Scheme.{w}}
    (sY : Y ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sY] (q : Y)
    [ValuationRing (Y.presheaf.stalk q)] :
    ∃ (Z : Scheme.{w}) (ν : Z ⟶ Y), IsNormalVariety k (ν ≫ sY) ∧ IsProjective ν ∧
      IsBirationalMorphism ν ∧ ∃ z : Z, ν z = q ∧ IsIso (ν.stalkMap z) := by
  let ν := normalizationOverField k sY
  have hX := finite_irreducibleComponents_of_locallyOfFiniteType k sY
  have hbir : IsBirational ν := Scheme.isBirational_normalization Y hX
  haveI : IsFinite ν := isFinite_normalizationOverField k sY
  haveI hvar : AlgebraicGeometry.IsVariety k (ν ≫ sY) := isVariety_normalizationOverField k sY
  haveI : IsIntegral (normalizationSchemeOverField k sY) := hvar.toIsIntegral
  have hνb : IsBirationalMorphism ν := isBirationalMorphism_of_isBirational ν hbir
  haveI : IsDominant ν := hνb.isDominant
  obtain ⟨z, hz⟩ := (Scheme.surjective_normalization Y hX).surj q
  refine ⟨_, ν, ⟨hvar, Scheme.isNormal_normalizationScheme Y hX⟩,
    Stacks.FiniteMorphismProjective.isProjective_of_isFinite ν, hνb, z, hz, ?_⟩
  subst hz
  exact isIso_stalkMap_of_valuationRing ν hνb.functionFieldMap_bijective.2 z

/-- A dominant morphism which is an open immersion on a dense open is birational. -/
private theorem isBirationalMorphism_of_isOpenImmersion {X Y : Scheme.{w}} (f : X ⟶ Y)
    [IsDominant f] (U : X.Opens) (hU : Dense (U : Set X)) [IsOpenImmersion (U.ι ≫ f)] :
    IsBirationalMorphism f := by
  have hd : Dense ((U.ι ≫ f).opensRange : Set Y) := by
    rw [Scheme.Hom.coe_opensRange, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    exact f.denseRange.dense_image f.continuous hU
  let e : X.PartialIso Y :=
    { source := U
      dense_source := hU
      target := (U.ι ≫ f).opensRange
      dense_target := hd
      iso := (U.ι ≫ f).isoOpensRange }
  refine ⟨e, ?_⟩
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff]
  refine ⟨U, hU, le_rfl, le_top, ?_⟩
  simp only [Scheme.PartialMap.restrict, Scheme.PartialIso.toPartialMap_hom,
    Scheme.Hom.toPartialMap_hom, e, Scheme.Hom.isoOpensRange_hom_ι]
  exact (Scheme.homOfLE_ι_assoc _ _ _).trans
    (by rw [Scheme.topIso_hom]; exact (Scheme.homOfLE_ι_assoc _ _ _).symm)

/-- A birational morphism is an open immersion on a dense open. -/
private theorem exists_isOpenImmersion_of_isBirationalMorphism {X Y : Scheme.{w}} {f : X ⟶ Y}
    (hf : IsBirationalMorphism f) :
    ∃ U : X.Opens, Dense (U : Set X) ∧ IsOpenImmersion (U.ι ≫ f) := by
  obtain ⟨e, he⟩ := hf
  rw [Scheme.PartialIso.toRationalMap, Scheme.PartialMap.toRationalMap_eq_iff] at he
  obtain ⟨W, hW, hWe, hWf, h⟩ := he
  simp only [Scheme.PartialMap.restrict_hom] at h
  have he' : IsOpenImmersion e.toPartialMap.hom := by
    change IsOpenImmersion (e.iso.hom ≫ e.target.ι)
    infer_instance
  refine ⟨W, hW, ?_⟩
  have : W.ι ≫ f = X.homOfLE hWf ≫ f.toPartialMap.hom := by
    change W.ι ≫ f = (X.homOfLE (le_top : W ≤ ⊤) ≫ X.topIso.hom) ≫ f
    simp only [Scheme.topIso_hom, Scheme.homOfLE_ι]
  rw [this, ← h]
  infer_instance

/-- A composite of birational morphisms out of an irreducible scheme is birational. -/
private theorem isBirationalMorphism_comp {X Y Z : Scheme.{w}} [IrreducibleSpace X]
    {f : X ⟶ Y} {g : Y ⟶ Z} (hf : IsBirationalMorphism f) (hg : IsBirationalMorphism g) :
    IsBirationalMorphism (f ≫ g) := by
  haveI := hf.isDominant
  haveI := hg.isDominant
  obtain ⟨U₁, hU₁, h₁⟩ := exists_isOpenImmersion_of_isBirationalMorphism hf
  obtain ⟨U₂, hU₂, h₂⟩ := exists_isOpenImmersion_of_isBirationalMorphism hg
  let U : X.Opens := U₁ ⊓ f ⁻¹ᵁ U₂
  have hne : (U : Set X).Nonempty := by
    obtain ⟨x₀⟩ := (IrreducibleSpace.isIrreducible_univ X).nonempty
    haveI : Nonempty Y := ⟨f x₀⟩
    have hd : Dense (f '' U₁) := f.denseRange.dense_image f.continuous hU₁
    obtain ⟨y, hy₂, x, hx₁, rfl⟩ := (hU₂.inter_of_isOpen_left hd U₂.2).nonempty
    exact ⟨x, hx₁, hy₂⟩
  have hU : Dense (U : Set X) := U.2.dense hne
  have hle : U ≤ f ⁻¹ᵁ U₂ := inf_le_right
  have hle₁ : U ≤ U₁ := inf_le_left
  have hres : IsOpenImmersion (f.resLE U₂ U hle) := by
    have : f.resLE U₂ U hle ≫ U₂.ι = X.homOfLE hle₁ ≫ (U₁.ι ≫ f) := by
      rw [Scheme.Hom.resLE_comp_ι, ← Category.assoc, Scheme.homOfLE_ι]
    have : IsOpenImmersion (f.resLE U₂ U hle ≫ U₂.ι) := by rw [this]; infer_instance
    exact IsOpenImmersion.of_comp _ U₂.ι
  haveI : IsOpenImmersion (U.ι ≫ f ≫ g) := by
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι f hle, Category.assoc]
    infer_instance
  exact isBirationalMorphism_of_isOpenImmersion (f ≫ g) U hU

/-- Transport of "the local ring at `ν z` is a given subset of `k(X)`" along a morphism `ν`
which is an isomorphism on local rings at `z`. -/
private theorem forall_iff_exists_stalk_comp {X Y Z : Scheme.{w}} [IsIntegral X] [IsIntegral Y]
    [IsIntegral Z] (ν : Z ⟶ Y) (β : Y ⟶ X) [IsDominant ν] [IsDominant β] [IsDominant (ν ≫ β)]
    (z : Z) [IsIso (ν.stalkMap z)] (S : Set X.functionField)
    (hq : ∀ g : X.functionField, g ∈ S ↔
      ∃ a : Y.presheaf.stalk (ν z), algebraMap _ Y.functionField a = functionFieldMap β g) :
    ∀ g : X.functionField, g ∈ S ↔
      ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap (ν ≫ β) g := by
  intro g
  rw [hq g]
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨(ν.stalkMap z).hom a, ?_⟩
    rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, ha,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply]
  · rintro ⟨b, hb⟩
    refine ⟨(inv (ν.stalkMap z)).hom b, (functionFieldMap ν).injective ?_⟩
    rw [MMP.Mori.functionFieldMap_algebraMap_stalk,
      MMP.Positivity.DivisorOver.functionFieldMap_functionFieldMap_apply, ← hb]
    congr 1
    exact congrArg (fun φ => φ.hom b) (IsIso.inv_hom_id (ν.stalkMap z))

/-- Two equivalent `ℤᵐ⁰`-valued valuations of a field which both take the value `exp (-1)` are
equal. -/
private theorem eq_of_isEquiv_of_exp_neg_one {K : Type*} [Field K] {w₁ w₂ : Valuation K ℤᵐ⁰}
    (h : w₁.IsEquiv w₂) (h₁ : ∃ a, w₁ a = WithZero.exp (-1))
    (h₂ : ∃ a, w₂ a = WithZero.exp (-1)) : w₁ = w₂ := by
  obtain ⟨ϖ, hϖ⟩ := h₁
  obtain ⟨ϖ', hϖ'⟩ := h₂
  have hpow : ∀ (w : Valuation K ℤᵐ⁰) (c : ℤ), w ϖ = WithZero.exp c → ∀ n : ℤ,
      w (ϖ ^ n) = WithZero.exp (c * n) := by
    intro w c hc n
    rw [map_zpow₀, hc, ← WithZero.exp_zsmul, smul_eq_mul, mul_comm]
  have hw₂ϖ : w₂ ϖ ≠ 0 := by
    rw [ne_eq, ← h.eq_zero, hϖ]; exact WithZero.exp_ne_zero
  set a := WithZero.log (w₂ ϖ)
  have ha : w₂ ϖ = WithZero.exp a := (WithZero.exp_log hw₂ϖ).symm
  have hw₁ϖ' : w₁ ϖ' ≠ 0 := by
    rw [ne_eq, h.eq_zero, hϖ']; exact WithZero.exp_ne_zero
  set b := WithZero.log (w₁ ϖ')
  have hb : w₁ ϖ' = WithZero.exp b := (WithZero.exp_log hw₁ϖ').symm
  have hab : w₂ ϖ' = WithZero.exp (a * -b) := by
    rw [← hpow w₂ a ha]
    exact (Valuation.IsEquiv.eq_iff h).mp (by rw [hb, hpow w₁ (-1) hϖ]; congr 1; ring)
  rw [hϖ', WithZero.exp_inj] at hab
  have ha0 : a < 0 := by
    have : w₂ ϖ < 1 := (Valuation.isEquiv_iff_val_lt_one.mp h).mp
      (by rw [hϖ, ← WithZero.exp_zero, WithZero.exp_lt_exp]; omega)
    rwa [ha, ← WithZero.exp_zero, WithZero.exp_lt_exp] at this
  have ha1 : a = -1 := by
    have : a * b = 1 := by linarith
    rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with h | h <;> omega
  ext g
  by_cases hg : g = 0
  · simp [hg]
  have hg1 : w₁ g ≠ 0 := by simp [hg]
  set m := WithZero.log (w₁ g)
  have hm : w₁ g = WithZero.exp m := (WithZero.exp_log hg1).symm
  have : w₂ g = w₂ (ϖ ^ (-m)) :=
    (Valuation.IsEquiv.eq_iff h).mp (by rw [hm, hpow w₁ (-1) hϖ]; congr 1; ring)
  rw [this, hpow w₂ a ha, hm, ha1]; congr 1; ring

/-- A divisor of the function field takes the value `exp (-1)`. -/
private theorem IsDivisorOfFunctionField.exists_eq_exp_neg_one {k : Type w} [Field k]
    {X : Scheme.{w}} (sX : X ⟶ Spec (.of k)) [IsIntegral X] {v : Valuation X.functionField ℤᵐ⁰}
    (hv : IsDivisorOfFunctionField k sX v) : ∃ g, v g = WithZero.exp (-1) := by
  obtain ⟨Y, sY, hY, E, hE⟩ := hv
  haveI : IsIntegral Y := hY.1.toIsIntegral
  haveI : IsNormal Y := hY.2
  haveI : IsLocallyNoetherian Y :=
    haveI := hY.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian sY
  letI := functionFieldAlgebra sX
  letI := functionFieldAlgebra sY
  obtain ⟨e, rfl⟩ := hE
  haveI := E.isDiscreteValuationRing_localRing
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible E.localRing
  refine ⟨e.symm (algebraMap E.localRing Y.functionField ϖ), ?_⟩
  rw [Valuation.comap_apply]
  simp only [RingHom.coe_coe, AlgEquiv.apply_symm_apply]
  exact E.divisorialValuation_algebraMap_of_irreducible hϖ

/-- If the local ring of `Z` at `z` is, inside `k(X)`, the valuation ring of a valuation taking
the value `exp (-1)`, it is not a field. -/
private theorem not_isField_stalk_of_forall_le_one_iff {X Z : Scheme.{w}} [IsIntegral X]
    [IsIntegral Z] (h : Z ⟶ X) [IsDominant h] (v : Valuation X.functionField ℤᵐ⁰) (z : Z)
    (hz : ∀ g : X.functionField, v g ≤ 1 ↔
      ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap h g)
    {g₀ : X.functionField} (hg₀ : v g₀ = WithZero.exp (-1)) :
    ¬ IsField (Z.presheaf.stalk z) := by
  intro hF
  obtain ⟨a, ha⟩ := (hz g₀).1 (by rw [hg₀, ← WithZero.exp_zero, WithZero.exp_le_exp]; omega)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, map_eq_zero, ← v.zero_iff, hg₀] at ha
    exact WithZero.exp_ne_zero ha
  obtain ⟨b, hb⟩ := hF.mul_inv_cancel ha0
  have hb' : v g₀⁻¹ ≤ 1 := (hz _).2 ⟨b, by
    rw [map_inv₀, ← ha]
    exact eq_inv_of_mul_eq_one_right (by rw [← map_mul, hb, map_one])⟩
  rw [map_inv₀, hg₀, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_zero, WithZero.exp_le_exp] at hb'
  omega

/-- **The assembly step.** On a normal locally noetherian integral scheme `Z` dominating `X`, a
point `z` whose local ring is, inside `k(X)`, the valuation ring of a valuation `v` of `k(X)`
taking the value `exp (-1)`, is the generic point of a prime divisor `F` with `ord_F = v`. -/
private theorem exists_primeDivisor_valuationOver_eq {X : Scheme.{w}} [IsIntegral X]
    {v : Valuation X.functionField ℤᵐ⁰} {g₀ : X.functionField}
    (hg₀ : v g₀ = WithZero.exp (-1)) {Z : Scheme.{w}} [IsIntegral Z]
    [IsLocallyNoetherian Z] [IsNormal Z] (h : Z ⟶ X) (hh : IsBirationalMorphism h) (z : Z)
    (hz : haveI : IsDominant h := hh.isDominant
      ∀ g : X.functionField, v g ≤ 1 ↔
        ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = functionFieldMap h g) :
    ∃ F : MMP.Mori.PrimeDivisor Z, F.genericPoint = z ∧
      haveI : IsDominant h := hh.isDominant
      F.valuationOver h = v := by
  haveI : IsDominant h := hh.isDominant
  haveI := valuationRing_stalk_of_forall_le_one_iff h hh v z hz
  have hnf := not_isField_stalk_of_forall_le_one_iff h v z hz hg₀
  haveI : IsDiscreteValuationRing (Z.presheaf.stalk z) :=
    ((IsDiscreteValuationRing.TFAE (Z.presheaf.stalk z) hnf).out 1 2).mpr ‹_›
  have hcoh : Order.coheight z = 1 := by
    have h1 := ringKrullDim_stalk_eq_coheight z
    rw [IsDiscreteValuationRing.ringKrullDim_eq_one] at h1
    exact_mod_cast h1.symm
  refine ⟨AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hcoh,
    AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hcoh, ?_⟩
  set F : MMP.Mori.PrimeDivisor Z := AlgebraicGeometry.PrimeDivisor.ofCoheightOne z hcoh
  have hF : F.genericPoint = z := AlgebraicGeometry.PrimeDivisor.genericPoint_ofCoheightOne z hcoh
  have hrange : ∀ r : Z.functionField,
      r ∈ (algebraMap F.localRing Z.functionField).range ↔
        ∃ a : Z.presheaf.stalk z, algebraMap _ Z.functionField a = r := by
    intro r
    change (∃ a : Z.presheaf.stalk F.genericPoint, _) ↔ _
    clear_value F
    subst hF
    rfl
  apply eq_of_isEquiv_of_exp_neg_one
  · refine Valuation.isEquiv_iff_val_le_one.mpr fun {g} => ?_
    rw [PrimeDivisor.valuationOver_apply, PrimeDivisor.divisorialValuation_le_one_iff, hrange,
      hz g]
  · haveI := F.isDiscreteValuationRing_localRing
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible F.localRing
    obtain ⟨g, hg⟩ := hh.functionFieldMap_bijective.2 (algebraMap F.localRing Z.functionField ϖ)
    refine ⟨g, ?_⟩
    rw [PrimeDivisor.valuationOver_apply, hg]
    exact F.divisorialValuation_algebraMap_of_irreducible hϖ
  · exact ⟨g₀, hg₀⟩

end MMP.Flips.Proof_lem_fa1a_valuation_realized_at_dominated_point

namespace MMP.Flips

open CategoryTheory AlgebraicGeometry

open MMP.Mori MMP.Flips
  MMP.Flips.Proof_lem_fa1a_valuation_realized_at_dominated_point in
/-- Let `X` be a variety over `k` and `v` a `ℤᵐ⁰`-valued valuation of `k(X)` taking the value
`exp (-1)`, whose valuation ring is the image of a `k`-algebra essentially of finite type and
dominates the local ring `𝒪_{X,x}` of a point `x`. Then there is a divisor `(Z, h, F)` over `X`
with `h` projective, valuation `ord_F = v` and `h(η_F) = x`. -/
public theorem exists_properDivisorOver_isProjective_of_dominates_of_essFiniteType {k : Type u}
    [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    {v : Valuation X.functionField ℤᵐ⁰}
    (hS : letI := functionFieldAlgebra sX
      ∃ (S : Type u) (_ : CommRing S) (_ : Algebra k S) (_ : Algebra.EssFiniteType k S)
        (φ : S →ₐ[k] X.functionField), ∀ g, v g ≤ 1 ↔ g ∈ φ.range)
    {g₀ : X.functionField} (hg₀ : v g₀ = WithZero.exp (-1)) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1) :
    ∃ D : ProperDivisorOver k sX, IsProjective D.f ∧ D.valuation = v ∧
      D.f D.E.genericPoint = x := by
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  obtain ⟨X₂, β, hvar₂, hβ, hprojβ, q, hqx, hq⟩ :=
    exists_blowUp_stalk_eq_integer sX hS x hle hlt
  haveI : IsIntegral X₂ := hvar₂.toIsIntegral
  haveI : IsDominant β := hβ.isDominant
  obtain ⟨Z, ν, hZ, hprojν, hν, z, hzq, hiso⟩ :=
    haveI := valuationRing_stalk_of_forall_le_one_iff β hβ v q hq
    exists_normalization_isIso_stalkMap (β ≫ sX) q
  subst hzq
  haveI : IsIntegral Z := hZ.1.toIsIntegral
  have hh : IsBirationalMorphism (ν ≫ β) := isBirationalMorphism_comp hν hβ
  have hZ' : IsNormalVariety k ((ν ≫ β) ≫ sX) := by rwa [Category.assoc]
  haveI : IsNormal Z := hZ.2
  haveI : IsLocallyNoetherian Z :=
    haveI : LocallyOfFiniteType ((ν ≫ β) ≫ sX) := hZ'.1.toLocallyOfFiniteType
    LocallyOfFiniteType.isLocallyNoetherian ((ν ≫ β) ≫ sX)
  haveI : IsDominant ν := hν.isDominant
  haveI : IsDominant (ν ≫ β) := hh.isDominant
  have hz := forall_iff_exists_stalk_comp ν β z {g | v g ≤ 1} hq
  obtain ⟨F, hFz, hFv⟩ := exists_primeDivisor_valuationOver_eq hg₀ (ν ≫ β) hh z hz
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  haveI : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated sX
  have hproj : IsProjective (ν ≫ β) :=
    IsProjective.comp hprojν hprojβ
  refine ⟨⟨⟨Z, ν ≫ β, hZ', hh, F⟩, hproj.isProper⟩, hproj, hFv, ?_⟩
  change (ν ≫ β) F.genericPoint = x
  rw [hFz, Scheme.Hom.comp_apply, hqx]

open CategoryTheory AlgebraicGeometry MMP.Mori MMP.Flips
  MMP.Flips.Proof_lem_fa1a_valuation_realized_at_dominated_point in
/-- Let `X` be a variety over `k` and `v` a divisor of `k(X)` whose valuation ring dominates the
local ring `𝒪_{X,x}` of a point `x`. Then there is a divisor `(Z, h, F)` over `X` with `h`
projective, valuation `ord_F = v` and `h(η_F) = x`. -/
@[mmp "lem_fa1a_valuation_realized_at_dominated_point"]
public theorem exists_properDivisorOver_isProjective_of_dominates {k : Type u} [Field k]
    {X : Scheme.{u}} (sX : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsVariety k sX]
    {v : Valuation X.functionField ℤᵐ⁰} (hv : IsDivisorOfFunctionField k sX v) (x : X)
    (hle : ∀ a : X.presheaf.stalk x, v (algebraMap _ X.functionField a) ≤ 1)
    (hlt : ∀ a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x),
      v (algebraMap _ X.functionField a) < 1) :
    ∃ D : ProperDivisorOver k sX, IsProjective D.f ∧ D.valuation = v ∧
      D.f D.E.genericPoint = x := by
  haveI : IsIntegral X := ‹AlgebraicGeometry.IsVariety k sX›.toIsIntegral
  obtain ⟨g₀, hg₀⟩ := IsDivisorOfFunctionField.exists_eq_exp_neg_one sX hv
  exact exists_properDivisorOver_isProjective_of_dominates_of_essFiniteType sX
    (IsDivisorOfFunctionField.exists_essFiniteType sX hv) hg₀ x hle hlt

end MMP.Flips

/-!
## Exceptional divisors and the exceptional set

For a proper birational morphism `f : Y ⟶ X` of normal varieties and a prime divisor `P` of `Y`,
`P` lies in the exceptional set `Ex(f)` if and only if the divisor `(Y, f, P)` over `X` is
exceptional, i.e. `dim f(P) ≤ dim X - 2`.

#### Main results

* `MMP.Flips.ProperDivisorOver.support_subset_exceptionalSet_iff`

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 2.16
-/

namespace MMP.Flips.Proof_lem_fa2_exceptional_divisor_iff_in_exceptional_set

open CategoryTheory AlgebraicGeometry

/-- A local ring `S ⊆ K` which contains a valuation subring `R` of `K`, with the nonunits of `R`
in the maximal ideal of `S`, is contained in `R` and dominated by it. -/
private theorem forall_mem_of_dominates {K : Type*} [Field K] (R : ValuationSubring K)
    {S : Type*} [CommRing S] [IsLocalRing S] (i : S →+* K) (hi : Function.Injective i)
    (hR : ∀ g ∈ R, ∃ c, i c = g ∧ (g ∈ R.nonunits → c ∈ IsLocalRing.maximalIdeal S)) :
    (∀ a, i a ∈ R) ∧ ∀ a ∈ IsLocalRing.maximalIdeal S, i a ∈ R.nonunits := by
  have h1 : ∀ a, i a ∈ R := by
    intro a
    by_contra ha
    have h0 : i a ≠ 0 := fun h => ha (h ▸ R.zero_mem)
    have hinv : (i a)⁻¹ ∈ R.nonunits :=
      R.mem_nonunits_iff_or.mpr (Or.inr (by rwa [inv_inv]))
    obtain ⟨c, hc, hcm⟩ := hR _ ((R.mem_or_inv_mem _).resolve_left ha)
    have : a * c = 1 := hi (by rw [map_mul, hc, map_one, mul_inv_cancel₀ h0])
    exact (IsLocalRing.mem_maximalIdeal _).mp (hcm hinv) (IsUnit.of_mul_eq_one_right _ this)
  refine ⟨h1, fun a ha => ?_⟩
  refine R.mem_nonunits_iff_or.mpr (or_iff_not_and_not.mpr fun ⟨h0, hinv⟩ => ?_)
  obtain ⟨c, hc, -⟩ := hR _ (not_not.mp hinv)
  have : a * c = 1 := hi (by rw [map_mul, hc, map_one, mul_inv_cancel₀ h0])
  exact (IsLocalRing.mem_maximalIdeal _).mp ha (IsUnit.of_mul_eq_one _ this)

/-- A germ at `x'` is a germ at any point `x = x'`, with the same image in the function field and
the same membership in the maximal ideal. -/
private theorem exists_stalk_of_eq {X : Scheme.{w}} [IsIntegral X] {x x' : X} (h : x = x')
    (b : X.presheaf.stalk x') : ∃ b' : X.presheaf.stalk x,
      algebraMap _ X.functionField b' = algebraMap _ X.functionField b ∧
        (b' ∈ IsLocalRing.maximalIdeal _ ↔ b ∈ IsLocalRing.maximalIdeal _) := by
  subst h
  exact ⟨b, rfl, Iff.rfl⟩

/-- A dimension `b = a + 1` which is finite and nonnegative is not `≥ a + 2`. -/
private theorem not_add_two_le_of_add_one_eq {a b : WithBot ℕ∞} (hb : b ≠ ⊤) (h0 : 0 ≤ b)
    (hab : a + 1 = b) : ¬ a + 2 ≤ b := by
  subst hab
  induction a using WithBot.recBotCoe with
  | bot => simp at h0
  | coe a =>
    induction a using ENat.recTopCoe with
    | top => exact absurd rfl hb
    | coe a =>
      intro h
      have : (((a + 2 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((a + 1 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
        simpa using h
      have : a + 2 ≤ a + 1 := by exact_mod_cast WithBot.coe_le_coe.mp this
      omega

/-- If a point `y` of `P` has a neighbourhood on which `f` is an open immersion, then `(Y, f, P)`
is not exceptional: `f` preserves the coheight `1` of the generic point of `P`. -/
private theorem not_isExceptional_of_notMem_exceptionalSet {k : Type w} [Field k]
    {X : Scheme.{w}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsNormalVariety k sX)
    (D : MMP.Flips.ProperDivisorOver k sX) {y : D.Y} (hy : y ∈ (D.E.support : Set D.Y))
    (hyE : y ∉ MMP.Flips.exceptionalSet D.f) : ¬ D.IsExceptional := by
  obtain ⟨V, hyV, hV⟩ := MMP.Flips.exists_isOpenImmersion_of_notMem_exceptionalSet hyE
  have hspec : D.E.genericPoint ⤳ y := by
    rwa [specializes_iff_mem_closure, ← AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  have hηE : D.E.genericPoint ∉ MMP.Flips.exceptionalSet D.f :=
    fun h => h ⟨V, hspec.mem_open V.isOpen hyV, hV⟩
  have := hX.1
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have hd := MMP.Flips.topologicalKrullDim_closure_singleton_add_coheight sX
    (D.f D.E.genericPoint)
  rw [MMP.Flips.coheight_map_of_notMem_exceptionalSet hηE,
    ← MMP.Flips.codimension_closureSingleton, D.E.codimension_closure_genericPoint] at hd
  unfold MMP.Flips.ProperDivisorOver.IsExceptional
  rw [D.center_eq_toDivisorOver_center, D.toDivisorOver.center_eq_closure_genericPoint]
  exact not_add_two_le_of_add_one_eq (topologicalKrullDim_ne_top_of_locallyOfFiniteType k sX)
    (Order.krullDim_nonneg_iff.mpr
      ⟨TopologicalSpace.IrreducibleCloseds.closureSingleton (genericPoint X)⟩) hd

/-- If `(Y, f, P)` is not exceptional, the generic point of `P` is the only point of `Y` over
its image: every such point has local ring dominated by the valuation ring
`𝒪_{Y,η_P} = 𝒪_{X,f(η_P)}`, and the centre of a valuation on the separated `Y` is unique. -/
private theorem eq_genericPoint_of_map_eq {k : Type w} [Field k]
    {X : Scheme.{w}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsNormalVariety k sX)
    (D : MMP.Flips.ProperDivisorOver k sX) (hD : ¬ D.IsExceptional) {y : D.Y}
    (hy : D.f y = D.f D.E.genericPoint) : y = D.E.genericPoint := by
  have := hX.1.toIsIntegral
  have := hX.2
  have := hX.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  obtain ⟨P, -, hη, hloc, -⟩ := D.exists_primeDivisor_of_not_isExceptional hX hD
  have := D.isIntegral
  have := D.isNormal
  have := D.isLocallyNoetherian
  have := D.isDominant
  have := D.isProper
  have := D.isNormalVariety.1
  have hbij := D.isBirationalMorphism.functionFieldMap_bijective
  let R := D.E.divisorialValuation.valuationSubring
  have hRmem : ∀ g, g ∈ R ↔ g ∈ (algebraMap D.E.localRing D.Y.functionField).range :=
    fun g => (Valuation.mem_valuationSubring_iff _ _).trans (D.E.divisorialValuation_le_one_iff g)
  -- the generic point of `P` is the centre of `R`
  have hηR := forall_mem_of_dominates R (algebraMap D.E.localRing D.Y.functionField)
    (IsFractionRing.injective _ _) fun g hg => by
      obtain ⟨c, rfl⟩ := (hRmem g).mp hg
      refine ⟨c, rfl, fun hn => (IsLocalRing.mem_maximalIdeal _).mpr fun hc => ?_⟩
      rcases R.mem_nonunits_iff_or.mp hn with h0 | hinv
      · rw [← map_zero (algebraMap D.E.localRing D.Y.functionField)] at h0
        exact not_isUnit_zero (IsFractionRing.injective _ _ h0 ▸ hc)
      · refine hinv ((hRmem _).mpr ⟨↑hc.unit⁻¹, ?_⟩)
        refine eq_inv_of_mul_eq_one_left ?_
        rw [← map_mul]
        simp
  -- every point over `f(η_P)` is a centre of `R`
  have hyR := forall_mem_of_dominates R (algebraMap (D.Y.presheaf.stalk y) D.Y.functionField)
    (IsFractionRing.injective _ _) fun g hg => by
      obtain ⟨h, rfl⟩ := hbij.2 g
      have hh : h ∈ (algebraMap P.localRing X.functionField).range := by
        rw [← hloc, Subring.mem_comap, ← hRmem]
        exact hg
      obtain ⟨b, rfl⟩ := hh
      obtain ⟨b', hb', hbm⟩ := exists_stalk_of_eq (hy.trans hη) b
      refine ⟨(D.f.stalkMap y).hom b', ?_, fun hn => ?_⟩
      · rw [← MMP.Mori.functionFieldMap_algebraMap_stalk, hb']
      · have hb : b ∈ IsLocalRing.maximalIdeal _ := by
          refine (IsLocalRing.mem_maximalIdeal _).mpr fun hu => ?_
          rcases R.mem_nonunits_iff_or.mp hn with h0 | hinv
          · have h0' : algebraMap _ X.functionField b = 0 := by
              rw [← map_zero (functionFieldMap D.f)] at h0
              exact hbij.1 h0
            rw [← map_zero (algebraMap P.localRing X.functionField)] at h0'
            exact not_isUnit_zero (IsFractionRing.injective _ _ h0' ▸ hu)
          · have hmem : functionFieldMap D.f
                (algebraMap P.localRing X.functionField ↑hu.unit⁻¹) ∈ R := by
              rw [hRmem, ← Subring.mem_comap, hloc]
              exact ⟨_, rfl⟩
            have heq : functionFieldMap D.f
                (algebraMap P.localRing X.functionField ↑hu.unit⁻¹) =
                  (functionFieldMap D.f (algebraMap P.localRing X.functionField b))⁻¹ := by
              refine eq_inv_of_mul_eq_one_left ?_
              rw [← map_mul, ← map_mul]
              simp
            exact hinv (heq ▸ hmem)
        exact (IsLocalRing.mem_maximalIdeal _).mpr fun hu =>
          (IsLocalRing.mem_maximalIdeal _).mp (hbm.mpr hb) (isUnit_of_map_unit _ _ hu)
  exact MMP.Flips.eq_of_isLocal_le_valuationSubring (D.f ≫ sX) R hyR.1 hyR.2 hηR.1 hηR.2

/-- If `(Y, f, P)` is not exceptional, the generic point of `P` is not in `Ex(f)`: the fibre
over its image is finite, so Zariski's main theorem makes `f` an isomorphism near it. -/
private theorem genericPoint_notMem_exceptionalSet {k : Type w} [Field k]
    {X : Scheme.{w}} {sX : X ⟶ Spec (.of k)} (hX : MMP.Mori.IsNormalVariety k sX)
    (D : MMP.Flips.ProperDivisorOver k sX) (hD : ¬ D.IsExceptional) :
    D.E.genericPoint ∉ MMP.Flips.exceptionalSet D.f := by
  have := hX.2
  have := hX.1
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian sX
  have := D.isIntegral
  have := D.isNormal
  have := D.isProper
  have hfin : (D.f ⁻¹' {D.f D.E.genericPoint}).Finite :=
    (Set.finite_singleton D.E.genericPoint).subset fun _ => eq_genericPoint_of_map_eq hX D hD
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace sX
  have : IsNoetherian X := ⟨⟩
  have hbir : AlgebraicGeometry.IsBirational D.f :=
    MMP.Resolution.Bridges.isBirational_of_isBirationalMorphism D.isBirationalMorphism
  have := IsNormal.stalk_normal (X := X) (D.f D.E.genericPoint)
  obtain ⟨U, hxU, hU⟩ := exists_isIso_restrict_of_finite_fiber_of_normal D.f hbir _ hfin
  intro h
  refine h ⟨D.f ⁻¹ᵁ U, hxU, ?_⟩
  rw [← morphismRestrict_ι]
  infer_instance

end MMP.Flips.Proof_lem_fa2_exceptional_divisor_iff_in_exceptional_set

namespace MMP.Flips.ProperDivisorOver

open CategoryTheory AlgebraicGeometry
  MMP.Flips.Proof_lem_fa2_exceptional_divisor_iff_in_exceptional_set in
/-- A prime divisor `P` of `Y` lies in the exceptional set of a proper birational morphism
`f : Y ⟶ X` of normal varieties if and only if `(Y, f, P)` is an exceptional divisor over `X`. -/
@[mmp "lem_fa2_exceptional_divisor_iff_in_exceptional_set"]
public theorem support_subset_exceptionalSet_iff {k : Type u} [Field k] {X : Scheme.{u}}
    {sX : X ⟶ Spec (.of k)} (hX : Mori.IsNormalVariety k sX) (D : ProperDivisorOver k sX) :
    (D.E.support : Set D.Y) ⊆ exceptionalSet D.f ↔ D.IsExceptional := by
  refine ⟨fun h => by_contra fun hD => genericPoint_notMem_exceptionalSet hX D hD (h ?_),
    fun hD y hy => by_contra fun hyE => not_isExceptional_of_notMem_exceptionalSet hX D hy hyE hD⟩
  rw [AlgebraicGeometry.PrimeDivisor.support_eq_closure]
  exact subset_closure rfl

end MMP.Flips.ProperDivisorOver

/-!
## Existence and uniqueness of the log discrepancy vector of a weighted graph

A weighted graph `Γ` whose matrix `M(Γ)` is nondegenerate, i.e. `Δ(Γ) = det(-M(Γ)) ≠ 0`, has
exactly one log discrepancy vector `a(Γ) ∈ ℚ^{V(Γ)}`: the defining equations
`∑_k a_k M(Γ)_{kj} = -c_j(Γ)` form a square linear system with invertible matrix. This applies
in particular to every negative definite weighted graph, whose determinant `Δ(Γ)` is positive.

#### Main results

* `MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`: if `Δ(Γ) ≠ 0`, then `Γ` has
  a unique log discrepancy vector.

#### Implementation notes

The source states the result for negative definite `Γ`; only the nondegeneracy `Δ(Γ) ≠ 0`
of `M(Γ)` enters, and negative definiteness implies it (`Matrix.PosDef.det_pos` applied to
`-M(Γ)` over `ℚ`).

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.3)
-/

namespace MMP.Flips.Proof_lem_fa3_graph_log_discrepancy_vector_exists_unique

open Matrix MMP.Flips MMP.Flips.WeightedGraph

/-- The log discrepancy equations `∑ₖ aₖ (Eₖ·Eⱼ) = -cⱼ` are the row-vector equation
`a ᵥ* M(Γ) = -c` over `ℚ`. -/
private lemma isLogDiscrepancyVector_iff_vecMul {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : WeightedGraph V) (a : V → ℚ) :
    Γ.IsLogDiscrepancyVector a ↔ a ᵥ* Γ.matrix.map ((↑) : ℤ → ℚ) = -Γ.c := by
  simp [IsLogDiscrepancyVector, funext_iff, Matrix.vecMul, dotProduct]

/-- `det(-M(Γ)) ≠ 0` makes the rational intersection matrix invertible. -/
private lemma isUnit_det_matrix_map {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : WeightedGraph V) (hΓ : Γ.det ≠ 0) : IsUnit (Γ.matrix.map ((↑) : ℤ → ℚ)).det := by
  rw [← Int.cast_det, isUnit_iff_ne_zero, Int.cast_ne_zero]
  simpa [WeightedGraph.det, Matrix.det_neg] using hΓ

end MMP.Flips.Proof_lem_fa3_graph_log_discrepancy_vector_exists_unique

namespace MMP.Flips.WeightedGraph

open Matrix MMP.Flips MMP.Flips.WeightedGraph
  MMP.Flips.Proof_lem_fa3_graph_log_discrepancy_vector_exists_unique in
/-- A weighted graph `Γ` with `Δ(Γ) = det(-M(Γ)) ≠ 0` — in particular every negative definite
weighted graph — has exactly one log discrepancy vector `a(Γ)`. -/
@[mmp "lem_fa3_graph_log_discrepancy_vector_exists_unique"]
public theorem existsUnique_isLogDiscrepancyVector {V : Type*} [Fintype V] [DecidableEq V]
    (Γ : WeightedGraph V) (hΓ : Γ.det ≠ 0) : ∃! a : V → ℚ, Γ.IsLogDiscrepancyVector a := by
  have h := isUnit_det_matrix_map Γ hΓ
  simp_rw [isLogDiscrepancyVector_iff_vecMul]
  refine ⟨-Γ.c ᵥ* (Γ.matrix.map ((↑) : ℤ → ℚ))⁻¹, by simp [Matrix.nonsing_inv_mul _ h], ?_⟩
  rintro b hb
  simp [← hb, Matrix.mul_nonsing_inv _ h]

end MMP.Flips.WeightedGraph

/-!
## A weighted graph with all `d_j = 0` is a Du Val graph

Let `Γ` be a weighted graph all of whose weights satisfy `n_j ≥ 1` and with no vertex having
`p_j = 0` and `n_j = 1`. If `d_j(Γ) = 2 - 2p_j - n_j - β_j = 0` for every vertex, then `Γ` is a
Du Val graph: since `p_j ≥ 0`, `β_j ≥ 0` and `n_j ≥ 1`, the equation `2p_j + n_j + β_j = 2`
forces `p_j = 0`, hence `n_j ∈ {1, 2}`, hence `n_j = 2` and `β_j = 0`.

#### Main results

* `MMP.Flips.WeightedGraph.isDuVal_of_forall_d_eq_zero`: under the hypotheses above, `Γ` is a
  Du Val graph.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.2)
-/

namespace MMP.Flips.Proof_lem_fa3_graph_dj_zero_du_val

open MMP.Flips

/-- The vertexwise statement: a vertex with `n_j ≥ 1`, not a smooth rational `(-1)`-vertex,
and with `d_j = 0` has `p_j = 0`, `n_j = 2` and `β_j = 0`. -/
private theorem du_val_vertex_of_d_eq_zero {V : Type*} [Fintype V] (Γ : WeightedGraph V)
    (j : V) (hn : 1 ≤ Γ.weight j) (hp : ¬(Γ.genus j = 0 ∧ Γ.weight j = 1)) (hd : Γ.d j = 0) :
    Γ.genus j = 0 ∧ Γ.weight j = 2 ∧ Γ.boundary j = 0 := by
  have hβ := Γ.boundary_nonneg j
  rw [WeightedGraph.d] at hd
  have hn' : (1 : ℚ) ≤ Γ.weight j := mod_cast hn
  have hg : Γ.genus j = 0 := by
    by_contra hne
    have : (1 : ℚ) ≤ Γ.genus j := mod_cast Nat.one_le_iff_ne_zero.mpr hne
    linarith
  have hw : Γ.weight j = 2 := by
    have : (Γ.weight j : ℚ) ≤ 2 := by simp only [hg, CharP.cast_eq_zero] at hd; linarith
    have : Γ.weight j ≤ 2 := mod_cast this
    have := fun h1 => hp ⟨hg, h1⟩
    omega
  refine ⟨hg, hw, ?_⟩
  simp only [hg, hw] at hd
  push_cast at hd
  linarith

end MMP.Flips.Proof_lem_fa3_graph_dj_zero_du_val

namespace MMP.Flips.WeightedGraph

open MMP.Flips MMP.Flips.Proof_lem_fa3_graph_dj_zero_du_val in
/-- A weighted graph with all weights `n_j ≥ 1`, no vertex with `p_j = 0` and `n_j = 1`, and
`d_j(Γ) = 0` for every vertex `v_j`, is a Du Val graph. -/
@[mmp "lem_fa3_graph_dj_zero_du_val"]
public theorem isDuVal_of_forall_d_eq_zero {V : Type*} [Fintype V] {Γ : WeightedGraph V}
    (hn : ∀ j, 1 ≤ Γ.weight j) (hp : ∀ j, ¬(Γ.genus j = 0 ∧ Γ.weight j = 1))
    (hd : ∀ j, Γ.d j = 0) : Γ.IsDuVal :=
  fun j => du_val_vertex_of_d_eq_zero _ j (hn j) (hp j) (hd j)

end MMP.Flips.WeightedGraph

/-!
## The log discrepancy vector of a single vertex of genus one vanishes

Let `Γ` be a weighted graph with a single vertex `v`, of genus `p = 1`, boundary degree
`β = 0` and weight `n`. Then `c_v(Γ) = 2 - 2p - β = 0` (there are no edges), and the equation
`a_v M(Γ)_{vv} = -n a_v = -c_v(Γ) = 0` has the unique solution `a_v = 0` as soon as `n ≠ 0`:
the log discrepancy vector of `Γ` is `(0)`.

#### Main results

* `MMP.Flips.WeightedGraph.isLogDiscrepancyVector_iff_eq_zero_of_genus_eq_one`: for a weighted
  graph `Γ` on a one-element vertex type with `p = 1`, `β = 0` and `n ≠ 0`, a vector `a` is a
  log discrepancy vector of `Γ` if and only if `a = 0`.

#### Implementation notes

The source assumes `n ≥ 1` (so that `Γ` is negative definite); only `n ≠ 0`, i.e.
`Δ(Γ) = n ≠ 0`, is needed. The single vertex is encoded by `[Unique V]`. The vector `a(Γ)` is
not a separate definition: the statement characterises the log discrepancy vectors of `Γ` as
exactly the zero vector, which contains both existence and uniqueness.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.4)
-/

namespace MMP.Flips.Proof_lem_fa3_genus_one_vertex_log_discrepancy_zero

open MMP.Flips MMP.Flips.WeightedGraph

/-- On a graph with a single vertex `v`, `a` is a log discrepancy vector iff `a_v n_v = c_v`. -/
private lemma isLogDiscrepancyVector_iff_of_unique {V : Type*} [Fintype V] [DecidableEq V]
    [Unique V] {Γ : WeightedGraph V} {a : V → ℚ} :
    Γ.IsLogDiscrepancyVector a ↔ a default * Γ.weight default = Γ.c default := by
  simp [IsLogDiscrepancyVector, Unique.forall_iff, matrix]

/-- A single vertex of genus `1` and boundary degree `0` has `c_v = 0`. -/
private lemma c_eq_zero_of_unique {V : Type*} [Fintype V] [DecidableEq V] [Unique V]
    {Γ : WeightedGraph V} (hp : Γ.genus default = 1) (hβ : Γ.boundary default = 0) :
    Γ.c default = 0 := by
  simp [c, hp, hβ, Finset.univ_unique]

end MMP.Flips.Proof_lem_fa3_genus_one_vertex_log_discrepancy_zero

namespace MMP.Flips.WeightedGraph

open MMP.Flips MMP.Flips.WeightedGraph
  MMP.Flips.Proof_lem_fa3_genus_one_vertex_log_discrepancy_zero in
/-- A weighted graph `Γ` with a single vertex of genus `1`, boundary degree `0` and nonzero
weight (in particular weight `n ≥ 1`) has log discrepancy vector `0`: `a` is a log discrepancy
vector of `Γ` if and only if `a = 0`. -/
@[mmp "lem_fa3_genus_one_vertex_log_discrepancy_zero"]
public theorem isLogDiscrepancyVector_iff_eq_zero_of_genus_eq_one {V : Type*} [Fintype V]
    [DecidableEq V] [Unique V] {Γ : WeightedGraph V} (hp : Γ.genus default = 1)
    (hβ : Γ.boundary default = 0) (hn : Γ.weight default ≠ 0) {a : V → ℚ} :
    Γ.IsLogDiscrepancyVector a ↔ a = 0 := by
  rw [isLogDiscrepancyVector_iff_of_unique, c_eq_zero_of_unique hp hβ, funext_iff,
    Unique.forall_iff]
  simp [hn]

end MMP.Flips.WeightedGraph

/-!
## The log discrepancy vector of a circle vanishes

Let `Γ` be a circle of smooth rational curves of length `l ≥ 2`. Every vertex has genus `0`,
boundary `0` and total edge weight `∑_{k ≠ j} m_{jk} = 2`, so `c_j(Γ) = 0` for all `j`, and the
zero vector solves the system `∑_k a_k M(Γ)_{kj} = -c_j(Γ)`. When `Δ(Γ) ≠ 0` — in particular when
`Γ` is negative definite — the solution is unique, so the log discrepancy vector of `Γ` is `0`.

#### Main results

* `MMP.Flips.WeightedGraph.isLogDiscrepancyVector_iff_eq_zero_of_isCircle`: for a circle `Γ`
  with `Δ(Γ) ≠ 0`, a vector `a` is a log discrepancy vector of `Γ` if and only if `a = 0`.

#### Implementation notes

The source assumes `Γ` negative definite; only the nondegeneracy `Δ(Γ) ≠ 0` of `M(Γ)` is used,
and negative definiteness implies it. The vector `a(Γ)` is not a separate definition: the
statement characterises the log discrepancy vectors of `Γ` as exactly the zero vector.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.5)
-/

namespace MMP.Flips.Proof_lem_fa3_circle_log_discrepancies_zero

open Finset MMP.Flips MMP.Flips.WeightedGraph

private theorem val_one_of_two_le {l : ℕ} [NeZero l] (hl : 2 ≤ l) : ((1 : Fin l) : ℕ) = 1 := by
  rw [Fin.val_one', Nat.one_mod_eq_one.2 (by omega)]

/-- The circle's adjacency relation on `Fin l`, read in the additive group `Fin l`. -/
private theorem circleAdj_iff {l : ℕ} [NeZero l] (hl : 2 ≤ l) (i j : Fin l) :
    (((i : ℕ) + 1) % l = j ∨ ((j : ℕ) + 1) % l = i) ↔ (j = i + 1 ∨ j = i - 1) := by
  rw [eq_sub_iff_add_eq, Fin.ext_iff, Fin.ext_iff, Fin.val_add, Fin.val_add,
    val_one_of_two_le hl]
  tauto

/-- In `Fin l` with `l ≥ 3`, the two neighbours `i + 1` and `i - 1` of `i` are distinct. -/
private theorem add_one_ne_sub_one {l : ℕ} [NeZero l] (hl : 3 ≤ l) (i : Fin l) :
    i + 1 ≠ i - 1 := by
  rw [Ne, eq_sub_iff_add_eq, add_assoc, add_eq_left, Fin.ext_iff, Fin.val_add,
    val_one_of_two_le (by omega), Fin.val_zero, Nat.mod_eq_of_lt (by omega)]
  omega

/-- At a vertex of a circle, the edge weights sum to `2`. -/
private theorem sum_edgeWeight_eq_two {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {l : ℕ} {e : Fin l ≃ V} (hΓ : Γ.IsCircleOrder e) (i : Fin l) :
    ∑ k, (Γ.edgeWeight (e i) k : ℚ) = 2 := by
  rw [← Equiv.sum_comp e]
  obtain rfl | hl : l = 2 ∨ 3 ≤ l := by have := hΓ.two_le; omega
  · have h01 : Γ.edgeWeight (e 0) (e 1) = 2 := hΓ.edgeWeight_eq_of_eq_two rfl
    fin_cases i <;> simp [Γ.edgeWeight_self, h01, Γ.edgeWeight_symm (e 1)] <;> norm_num
  have : NeZero l := ⟨by omega⟩
  have key (j : Fin l) :
      (Γ.edgeWeight (e i) (e j) : ℚ) = if j = i + 1 ∨ j = i - 1 then 1 else 0 := by
    obtain rfl | hij := eq_or_ne i j
    · simp [Γ.edgeWeight_self, eq_sub_iff_add_eq, Fin.one_eq_zero_iff]
      omega
    · simp [hΓ.edgeWeight_eq_of_three_le hl i j hij, circleAdj_iff (by omega : 2 ≤ l)]
  simp_rw [key, sum_boole, filter_or, filter_eq', mem_univ, if_true, ← insert_eq,
    card_pair (add_one_ne_sub_one hl i)]
  norm_num

end MMP.Flips.Proof_lem_fa3_circle_log_discrepancies_zero

namespace MMP.Flips.WeightedGraph

open Finset MMP.Flips MMP.Flips.WeightedGraph
  MMP.Flips.Proof_lem_fa3_circle_log_discrepancies_zero in
/-- For a circle `Γ` of length `l` with `Δ(Γ) ≠ 0` (in particular a negative definite circle),
the log discrepancy vector of `Γ` is zero: `a` is a log discrepancy vector of `Γ` if and only if
`a = 0`. -/
@[mmp "lem_fa3_circle_log_discrepancies_zero"]
public theorem isLogDiscrepancyVector_iff_eq_zero_of_isCircle {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} {l : ℕ} (hΓ : Γ.IsCircle l) (hdet : Γ.det ≠ 0)
    {a : V → ℚ} : Γ.IsLogDiscrepancyVector a ↔ a = 0 := by
  obtain ⟨e, he⟩ := hΓ
  have hzero : Γ.IsLogDiscrepancyVector 0 := by
    intro j
    obtain ⟨i, rfl⟩ := e.surjective j
    have hs : ∑ k ∈ univ.erase (e i), (Γ.edgeWeight (e i) k : ℚ) = 2 := by
      rw [← sum_edgeWeight_eq_two he i, ← add_sum_erase _ _ (mem_univ (e i)),
        Γ.edgeWeight_self, Nat.cast_zero, zero_add]
    simp [WeightedGraph.c, hs, he.genus_eq_zero, he.boundary_eq_zero]
  obtain ⟨b, -, hb⟩ := existsUnique_isLogDiscrepancyVector Γ hdet
  exact ⟨fun h => (hb a h).trans (hb 0 hzero).symm, fun h => h ▸ hzero⟩

end MMP.Flips.WeightedGraph

/-!
## The log discrepancy vector of a chain ending in a fork of weight-two arms

Let `Γ` be a negative definite rational tree whose vertices are a chain `w_1, …, w_s`
(`s ≥ 1`) and two further vertices `u_1, u_2` of weight `2`, with edges `w_i w_{i+1}`,
`w_s u_1`, `w_s u_2` and no others, and with boundary `β = e_{w_1}`. Then
`c_{w_s}(Γ) = -1`, `c_{w_i}(Γ) = 0` for `i < s` and `c_{u_k}(Γ) = 1`, and the vector with
`a_{w_i} = 0` and `a_{u_k} = 1/2` solves `∑_k a_k M(Γ)_{kj} = -c_j(Γ)`. Negative definiteness
makes the solution unique, so this is the log discrepancy vector of `Γ`.

#### Main results

* `MMP.Flips.WeightedGraph.isLogDiscrepancyVector_iff_of_fork_of_boundary_eq_single`: for such
  `Γ`, a vector `a` is a log discrepancy vector of `Γ` if and only if `a_{w_i} = 0` for every
  `i` and `a_{u_k} = 1/2` for every `k`.

#### Implementation notes

The vertices are given by families `w : Fin s → V` and `u : Fin 2 → V` such that
`Sum.elim w u : Fin s ⊕ Fin 2 → V` is a bijection; the edges are prescribed by the edge weights
between every pair of these vertices, in the manner of
`MMP.Flips.WeightedGraph.IsChainOrder`. Both `u 0` and `u 1` are attached to `w (s - 1)`.
The vector `a(Γ)` is not a separate definition: the statement characterises the log
discrepancy vectors of `Γ`.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.6),
  Fig. 3 (10)
-/

namespace MMP.Flips.Proof_lem_fa3_case10_fork_zero

open Finset MMP.Flips MMP.Flips.WeightedGraph

/-- Summing over `V` is summing over the chain and the two arms. -/
private theorem sum_eq_add {V : Type*} [Fintype V] {s : ℕ} {w : Fin s → V} {u : Fin 2 → V}
    (hbij : Function.Bijective (Sum.elim w u)) (f : V → ℚ) :
    ∑ v, f v = ∑ i, f (w i) + ∑ k, f (u k) := by
  rw [← Fintype.sum_bijective _ hbij (f ∘ Sum.elim w u) f (fun _ => rfl), Fintype.sum_sum_type]
  rfl

/-- A negative definite weighted graph has nonzero determinant. -/
private theorem det_ne_zero_of_isNegDef {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hneg : Γ.IsNegDef) : Γ.det ≠ 0 := by
  unfold WeightedGraph.IsNegDef at hneg
  intro h0
  have hdet : (-(Γ.matrix.map ((↑) : ℤ → ℚ))).det = 0 := by
    rw [← Matrix.map_neg _ (fun _ => Int.cast_neg _), ← Int.cast_det]
    exact_mod_cast h0
  obtain ⟨v, hv, hMv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  simpa [hMv] using hneg.dotProduct_mulVec_pos hv

/-- The entries of `M(Γ)`. -/
private theorem matrix_apply {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V)
    (j k : V) : (Γ.matrix j k : ℚ) = if j = k then -(Γ.weight j : ℚ) else Γ.edgeWeight j k := by
  unfold WeightedGraph.matrix
  rw [Matrix.of_apply]
  split_ifs <;> simp

/-- On a rational tree, `c_j = 2 - β_j - ∑_k m_{jk}`. -/
private theorem c_eq_of_isRationalTree {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (j : V) :
    Γ.c j = 2 - Γ.boundary j - ∑ k, (Γ.edgeWeight j k : ℚ) := by
  rw [WeightedGraph.c, ← add_sum_erase _ _ (mem_univ j), Γ.edgeWeight_self, hΓ.genus_eq_zero]
  simp

/-- Exactly one index `i` of `Fin s` (`s ≥ 1`) has `i + 1 = s`. -/
private theorem sum_ite_succ_eq {s : ℕ} (hs : 0 < s) :
    ∑ i : Fin s, (if (i : ℕ) + 1 = s then (1 : ℚ) else 0) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun n => if n + 1 = s then (1 : ℚ) else 0)]
  have : ∀ n, (n + 1 = s) ↔ (s - 1 = n) := fun n => by omega
  simp_rw [this, Finset.sum_ite_eq, Finset.mem_range]
  simp [hs]

/-- In the chain `Fin s`, the index `x` has the neighbours `x + 1` (if `x + 1 < s`) and
`x - 1` (if `0 < x`). -/
private theorem sum_ite_adj_eq {s : ℕ} (x : Fin s) :
    ∑ i : Fin s, (if (x : ℕ) + 1 = i ∨ (i : ℕ) + 1 = x then (1 : ℚ) else 0) =
      (if (x : ℕ) + 1 < s then 1 else 0) + (if 0 < (x : ℕ) then 1 else 0) := by
  have h (i : Fin s) : (if (x : ℕ) + 1 = i ∨ (i : ℕ) + 1 = x then (1 : ℚ) else 0) =
      (if (x : ℕ) + 1 = i then 1 else 0) + (if (i : ℕ) + 1 = x then 1 else 0) := by
    split_ifs <;> norm_num <;> omega
  simp_rw [h, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range (fun n => if (x : ℕ) + 1 = n then (1 : ℚ) else 0),
    Fin.sum_univ_eq_sum_range (fun n => if n + 1 = (x : ℕ) then (1 : ℚ) else 0)]
  have : ∀ n, (n + 1 = (x : ℕ)) ↔ ((x : ℕ) - 1 = n ∧ 0 < (x : ℕ)) := fun n => by omega
  simp_rw [this, ite_and, Finset.sum_ite_eq, Finset.mem_range]
  have := x.isLt
  congr 1
  split_ifs <;> first | rfl | omega

/-- The heart of the computation: on the fork, every vector that is `0` on the chain and `1/2`
on the two arms is a log discrepancy vector. -/
private theorem isLogDiscrepancyVector_of_fork {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) {s : ℕ} (hs : 0 < s)
    {w : Fin s → V} {u : Fin 2 → V} (hbij : Function.Bijective (Sum.elim w u))
    (hn : ∀ k, Γ.weight (u k) = 2)
    (hww : ∀ i j : Fin s,
      Γ.edgeWeight (w i) (w j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0)
    (hwu : ∀ (i : Fin s) (k : Fin 2),
      Γ.edgeWeight (w i) (u k) = if (i : ℕ) + 1 = s then 1 else 0)
    (huu : ∀ k l : Fin 2, Γ.edgeWeight (u k) (u l) = 0)
    (hβ : ∀ v, Γ.boundary v = if v = w ⟨0, hs⟩ then 1 else 0) {a : V → ℚ}
    (haw : ∀ i, a (w i) = 0) (hau : ∀ k, a (u k) = 1 / 2) : Γ.IsLogDiscrepancyVector a := by
  have hwinj : Function.Injective w := hbij.1.comp Sum.inl_injective
  have huinj : Function.Injective u := hbij.1.comp Sum.inr_injective
  have hwu' (i : Fin s) (k : Fin 2) : w i ≠ u k := fun h => by
    simpa using hbij.1 (a₁ := Sum.inl i) (a₂ := Sum.inr k) h
  have hcast (i : Fin s) : ((if (i : ℕ) + 1 = s then 1 else 0 : ℕ) : ℚ) =
      if (i : ℕ) + 1 = s then 1 else 0 := by
    split_ifs <;> simp
  intro j
  rw [c_eq_of_isRationalTree hΓ, sum_eq_add hbij, sum_eq_add hbij]
  simp only [haw, hau, zero_mul, sum_const_zero, zero_add]
  obtain ⟨x | k, rfl⟩ := hbij.2 j
  · have h2 : Γ.boundary (w x) = if (x : ℕ) = 0 then 1 else 0 := by
      simp [hβ, hwinj.eq_iff, Fin.ext_iff]
    simp_rw [Sum.elim_inl, matrix_apply, if_neg (hwu' x _).symm, Γ.edgeWeight_symm (u _), h2,
      hww, hwu, hcast]
    push_cast
    rw [sum_ite_adj_eq]
    simp only [Fin.sum_univ_two]
    have := x.isLt
    split_ifs <;> norm_num <;> omega
  · rw [Sum.elim_inr, hβ, if_neg (hwu' _ k).symm]
    simp_rw [Γ.edgeWeight_symm (u k), hwu, hcast, huu, sum_ite_succ_eq hs, matrix_apply,
      huinj.eq_iff, hn, huu]
    fin_cases k <;> simp [Fin.sum_univ_two] <;> norm_num

end MMP.Flips.Proof_lem_fa3_case10_fork_zero

namespace MMP.Flips.WeightedGraph

open Finset MMP.Flips MMP.Flips.WeightedGraph MMP.Flips.Proof_lem_fa3_case10_fork_zero in
/-- Let `Γ` be a negative definite rational tree consisting of a chain `w 0, …, w (s - 1)`
with `1 ≤ s` and two vertices `u 0, u 1` of weight `2`, both joined to `w (s - 1)`, where
consecutive `w i` are joined and there are no other edges, and whose boundary degree is `1` at
`w 0` and `0` elsewhere. Then the log discrepancy vector of `Γ` is `0` at each `w i` and `1/2`
at each `u k`. -/
@[mmp "lem_fa3_case10_fork_zero"]
public theorem isLogDiscrepancyVector_iff_of_fork_of_boundary_eq_single {V : Type*}
    [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) {s : ℕ} (hs : 0 < s) {w : Fin s → V} {u : Fin 2 → V}
    (hbij : Function.Bijective (Sum.elim w u))
    (hn : ∀ k, Γ.weight (u k) = 2)
    (hww : ∀ i j : Fin s,
      Γ.edgeWeight (w i) (w j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0)
    (hwu : ∀ (i : Fin s) (k : Fin 2),
      Γ.edgeWeight (w i) (u k) = if (i : ℕ) + 1 = s then 1 else 0)
    (huu : ∀ k l : Fin 2, Γ.edgeWeight (u k) (u l) = 0)
    (hβ : ∀ v, Γ.boundary v = if v = w ⟨0, hs⟩ then 1 else 0) {a : V → ℚ} :
    Γ.IsLogDiscrepancyVector a ↔ (∀ i, a (w i) = 0) ∧ ∀ k, a (u k) = 1 / 2 := by
  have key {a : V → ℚ} := isLogDiscrepancyVector_of_fork hΓ hs hbij hn hww hwu huu hβ (a := a)
  set e := Equiv.ofBijective _ hbij
  let a₀ : V → ℚ := Sum.elim (fun _ => 0) (fun _ => 1 / 2) ∘ e.symm
  have ha₀w (i : Fin s) : a₀ (w i) = 0 := congrArg (Sum.elim _ _) (e.symm_apply_apply (.inl i))
  have ha₀u (k : Fin 2) : a₀ (u k) = 1 / 2 :=
    congrArg (Sum.elim (fun _ => 0) _) (e.symm_apply_apply (.inr k))
  obtain ⟨b, -, hb⟩ := existsUnique_isLogDiscrepancyVector Γ (det_ne_zero_of_isNegDef hneg)
  refine ⟨fun h => ?_, fun h => key h.1 h.2⟩
  rw [(hb a h).trans (hb a₀ (key ha₀w ha₀u)).symm]
  exact ⟨ha₀w, ha₀u⟩

end MMP.Flips.WeightedGraph

/-!
## The log discrepancy vector of a chain with boundary at both ends vanishes

Let `Γ` be a negative definite rational tree which is a weighted chain `w_1, …, w_s` with
`s ≥ 1`, whose boundary is `β = e_{w_1} + e_{w_s}`; for `s = 1` this means `β_{w_1} = 2`. Every
vertex then has `c_k(Γ) = 2 - β_k - deg w_k = 0`, so the zero vector solves the system
`∑_k a_k M(Γ)_{kj} = -c_j(Γ)`. Negative definiteness makes the solution unique, so the log
discrepancy vector of `Γ` is `0`.

#### Main results

* `MMP.Flips.WeightedGraph.isLogDiscrepancyVector_iff_eq_zero_of_isChainOrder`: for such `Γ`,
  a vector `a` is a log discrepancy vector of `Γ` if and only if `a = 0`.

#### Implementation notes

The chain is given by an enumeration `e : Fin s ≃ V` with
`MMP.Flips.WeightedGraph.IsChainOrder`. The source's two cases (`s ≥ 2` with
`β = e_{w_1} + e_{w_s}`, and `s = 1` with `β_{w_1} = 2`) are one condition: `β_{e i}` is the
number of ends among `e 0, e (s - 1)` that `i` indexes, counted with multiplicity. The vector
`a(Γ)` is not a separate definition: the statement characterises the log discrepancy vectors
of `Γ` as exactly the zero vector.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.3.3)
-/

namespace MMP.Flips.Proof_lem_fa3_case9_log_discrepancies_zero

open Finset MMP.Flips MMP.Flips.WeightedGraph

/-- At the vertex `e i` of a chain, the edge weights to the other vertices sum to
`[i ≠ 0] + [i + 1 ≠ s]`. -/
private theorem sum_erase_edgeWeight_eq {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V} (he : Γ.IsChainOrder e) (i : Fin s) :
    ∑ k ∈ univ.erase (e i), (Γ.edgeWeight (e i) k : ℚ) =
      (if (i : ℕ) = 0 then 0 else 1) + (if (i : ℕ) + 1 = s then 0 else 1) := by
  rw [sum_erase _ (by simp [Γ.edgeWeight_self]), ← e.sum_comp]
  have key (j : Fin s) : (Γ.edgeWeight (e i) (e j) : ℚ) =
      (if (j : ℕ) = i - 1 then (if (i : ℕ) = 0 then 0 else 1) else 0) +
        (if (j : ℕ) = i + 1 then 1 else 0) := by
    rw [he.edgeWeight_eq]
    split_ifs <;> simp_all <;> omega
  simp_rw [key, sum_add_distrib]
  rw [Fin.sum_univ_eq_sum_range
      (fun j => if j = (i : ℕ) - 1 then (if (i : ℕ) = 0 then (0 : ℚ) else 1) else 0),
    Fin.sum_univ_eq_sum_range (fun j => if j = (i : ℕ) + 1 then (1 : ℚ) else 0),
    sum_ite_eq', sum_ite_eq']
  have := i.isLt
  split_ifs <;> simp_all <;> omega

/-- On a chain with boundary `[i = 0] + [i + 1 = s]` at `e i`, every `c_j(Γ)` vanishes. -/
private theorem c_eq_zero {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {s : ℕ} {e : Fin s ≃ V} (he : Γ.IsChainOrder e)
    (hβ : ∀ i : Fin s, Γ.boundary (e i) =
      (if (i : ℕ) = 0 then 1 else 0) + (if (i : ℕ) + 1 = s then 1 else 0)) (j : V) :
    Γ.c j = 0 := by
  obtain ⟨i, rfl⟩ := e.surjective j
  rw [WeightedGraph.c, sum_erase_edgeWeight_eq he i, hβ i, he.genus_eq_zero i]
  split_ifs <;> norm_num

end MMP.Flips.Proof_lem_fa3_case9_log_discrepancies_zero

namespace MMP.Flips.WeightedGraph

open Finset MMP.Flips MMP.Flips.WeightedGraph
  MMP.Flips.Proof_lem_fa3_case9_log_discrepancies_zero in
/-- Let `Γ` be a negative definite rational tree which is a weighted chain enumerated by
`e : Fin s ≃ V` with `1 ≤ s`, whose boundary degree is `1` at each of the two ends `e 0` and
`e (s - 1)` (so `2` at the single vertex when `s = 1`) and `0` elsewhere. Then the log
discrepancy vector of `Γ` is zero: `a` is a log discrepancy vector of `Γ` if and only if
`a = 0`. -/
@[mmp "lem_fa3_case9_log_discrepancies_zero"]
public theorem isLogDiscrepancyVector_iff_eq_zero_of_isChainOrder {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    {s : ℕ} (hs : 0 < s) {e : Fin s ≃ V} (he : Γ.IsChainOrder e)
    (hβ : ∀ i : Fin s, Γ.boundary (e i) =
      (if (i : ℕ) = 0 then 1 else 0) + (if (i : ℕ) + 1 = s then 1 else 0))
    {a : V → ℚ} : Γ.IsLogDiscrepancyVector a ↔ a = 0 := by
  have hzero : Γ.IsLogDiscrepancyVector 0 := fun j => by simp [c_eq_zero he hβ j]
  obtain ⟨b, -, hb⟩ := existsUnique_isLogDiscrepancyVector Γ
    (MMP.Flips.Proof_lem_fa3_case10_fork_zero.det_ne_zero_of_isNegDef hneg)
  exact ⟨fun h => (hb a h).trans (hb 0 hzero).symm, fun h => h ▸ hzero⟩

end MMP.Flips.WeightedGraph

/-!
## The log discrepancy vector of the star with four arms of weight two

Let `Γ` be a weighted graph with all genera `p` and boundary degrees `β` equal to `0`, whose
vertices are a central vertex `v` and four further vertices `u_1, …, u_4` of weight `2`, each
joined to `v` by a simple edge and to nothing else. Then `c_v(Γ) = 2 - 4 = -2` and
`c_{u_k}(Γ) = 1`, and the vector with `a_v = 0` and `a_{u_k} = 1/2` solves the system
`∑_k a_k M(Γ)_{kj} = -c_j(Γ)`, whatever the weight of `v`. When `Δ(Γ) ≠ 0` — in particular when
`Γ` is negative definite — the solution is unique, so this is the log discrepancy vector of `Γ`.

#### Main results

* `MMP.Flips.WeightedGraph.isLogDiscrepancyVector_iff_of_four_arms`: for such `Γ` with
  `Δ(Γ) ≠ 0`, a vector `a` is a log discrepancy vector of `Γ` if and only if `a_v = 0` and
  `a_w = 1/2` for every `w ≠ v`.

#### Implementation notes

The source assumes `Γ` negative definite; only the nondegeneracy `Δ(Γ) ≠ 0` of `M(Γ)` is used
(here `Δ(Γ) = 16 (n_v - 2)`), and negative definiteness implies it. The four outer vertices are
an injective family `u : Fin 4 → V` whose range is the complement of `{v}`.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Chapter 3
-/

namespace MMP.Flips.Proof_lem_fa3_four_arm_lc_if

open MMP.Flips MMP.Flips.WeightedGraph Finset

/-- A sum over `V = {v} ⊔ range u` splits as the value at `v` plus the sum over the `u k`. -/
private theorem sum_split {V : Type*} [Fintype V] [DecidableEq V] {v : V} {u : Fin 4 → V}
    (hu : Function.Injective u) (hrange : Set.range u = {v}ᶜ) (f : V → ℚ) :
    ∑ w, f w = f v + ∑ k, f (u k) := by
  rw [Fintype.sum_eq_add_sum_compl v f]
  congr 1
  have : ({v}ᶜ : Finset V) = univ.map ⟨u, hu⟩ := by
    ext w
    simpa [eq_comm] using congrArg (w ∈ ·) hrange.symm
  rw [this, Finset.sum_map]
  rfl

/-- `c_j` with the sum over `k ≠ j` taken over all `k`, using `m_{jj} = 0`. -/
private theorem c_eq {V : Type*} [Fintype V] [DecidableEq V] (Γ : WeightedGraph V) (j : V) :
    Γ.c j = 2 - 2 * Γ.genus j - Γ.boundary j - ∑ k, (Γ.edgeWeight j k : ℚ) := by
  rw [c, Finset.sum_erase _ (by simp [Γ.edgeWeight_self])]

/-- The four-armed star: a rational centre `v` of genus `0` joined by simple edges to four
pairwise non-adjacent `(-2)`-curves, all without boundary, has log discrepancy vector
`0` at the centre and `1/2` on each arm. No determinant hypothesis is needed for existence. -/
private theorem isLogDiscrepancyVector_fourArm {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {v : V} {u : Fin 4 → V} (hu : Function.Injective u)
    (hrange : Set.range u = {v}ᶜ) (hp : ∀ w, Γ.genus w = 0) (hβ : ∀ w, Γ.boundary w = 0)
    (hn : ∀ k, Γ.weight (u k) = 2) (hvu : ∀ k, Γ.IsSimpleEdge v (u k))
    (huu : ∀ k l, k ≠ l → Γ.edgeWeight (u k) (u l) = 0) :
    Γ.IsLogDiscrepancyVector fun w => if w = v then 0 else 1 / 2 := by
  have huv k : u k ≠ v := (hvu k).1.symm
  have hm k : Γ.edgeWeight (u k) v = 1 := by rw [Γ.edgeWeight_symm, (hvu k).2]
  have hmuu k l : Γ.edgeWeight (u k) (u l) = 0 := by
    obtain rfl | h := eq_or_ne k l
    · exact Γ.edgeWeight_self _
    · exact huu k l h
  intro j
  rw [c_eq, sum_split hu hrange, sum_split hu hrange]
  by_cases hj : j = v
  · subst hj
    simp [matrix, huv, hm, (hvu _).2, hp, hβ, Γ.edgeWeight_self, Fin.sum_univ_four]
    norm_num
  · obtain ⟨l, rfl⟩ : j ∈ Set.range u := by rw [hrange]; exact hj
    simp [matrix, huv, hm, hmuu, hn, hp, hβ, hu.eq_iff]
    norm_num

end MMP.Flips.Proof_lem_fa3_four_arm_lc_if

namespace MMP.Flips.WeightedGraph

open MMP.Flips MMP.Flips.WeightedGraph Finset MMP.Flips.Proof_lem_fa3_four_arm_lc_if in
/-- Let `Γ` be a weighted graph with all genera and boundary degrees `0`, consisting of a
vertex `v` and four vertices `u 0, …, u 3` of weight `2`, each joined to `v` by a simple edge
and to no other vertex. If `Δ(Γ) ≠ 0` (in particular if `Γ` is negative definite), then the log
discrepancy vector of `Γ` is `0` at `v` and `1/2` at each `u k`. -/
@[mmp "lem_fa3_four_arm_lc_if"]
public theorem isLogDiscrepancyVector_iff_of_four_arms {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} {v : V} {u : Fin 4 → V}
    (hu : Function.Injective u) (hrange : Set.range u = {v}ᶜ)
    (hp : ∀ w, Γ.genus w = 0) (hβ : ∀ w, Γ.boundary w = 0)
    (hn : ∀ k, Γ.weight (u k) = 2) (hvu : ∀ k, Γ.IsSimpleEdge v (u k))
    (huu : ∀ k l, k ≠ l → Γ.edgeWeight (u k) (u l) = 0) (hdet : Γ.det ≠ 0) {a : V → ℚ} :
    Γ.IsLogDiscrepancyVector a ↔ a = fun w => if w = v then 0 else 1 / 2 := by
  have hb := isLogDiscrepancyVector_fourArm hu hrange hp hβ hn hvu huu
  obtain ⟨b, -, huniq⟩ := existsUnique_isLogDiscrepancyVector Γ hdet
  exact ⟨fun ha => (huniq a ha).trans (huniq _ hb).symm, fun h => h ▸ hb⟩

end MMP.Flips.WeightedGraph

/-!
## The log discrepancy vector of the chain with two forks of weight-two arms

Let `Γ` be a weighted graph with all genera `p` and boundary degrees `β` equal to `0`, whose
vertices are a chain `w_1, …, w_s` (`s ≥ 2`) and four further vertices `u_1, …, u_4` of weight
`2`, with simple edges `w_i w_{i+1}`, `w_1 u_1`, `w_1 u_2`, `w_s u_3`, `w_s u_4` and no others.
Then `c_{w_1}(Γ) = c_{w_s}(Γ) = -1`, `c_{w_i}(Γ) = 0` for `1 < i < s` and `c_{u_k}(Γ) = 1`, and
the vector with `a_{w_i} = 0` and `a_{u_k} = 1/2` solves the system
`∑_k a_k M(Γ)_{kj} = -c_j(Γ)`, whatever the weights of the `w_i`. When `Δ(Γ) ≠ 0` — in
particular when `Γ` is negative definite — the solution is unique, so this is the log
discrepancy vector of `Γ`.

#### Main results

* `MMP.Flips.WeightedGraph.isLogDiscrepancyVector_iff_of_two_forks`: for such `Γ` with
  `Δ(Γ) ≠ 0`, a vector `a` is a log discrepancy vector of `Γ` if and only if `a_{w_i} = 0` for
  every `i` and `a_{u_k} = 1/2` for every `k`.

#### Implementation notes

The source assumes `Γ` negative definite; only the nondegeneracy `Δ(Γ) ≠ 0` of `M(Γ)` is used,
and negative definiteness implies it. The vertices are given by families `w : Fin s → V` and
`u : Fin 4 → V` such that `Sum.elim w u : Fin s ⊕ Fin 4 → V` is a bijection; the edges are
prescribed by the edge weights between every pair of these vertices, in the manner of
`MMP.Flips.WeightedGraph.IsChainOrder`. Here `u 0, u 1` are attached to `w 0` and `u 2, u 3`
to `w (s - 1)`.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.2.5)
-/

namespace MMP.Flips.Proof_lem_fa3_two_fork_lc_if

open MMP.Flips MMP.Flips.WeightedGraph Finset

/-- The number of neighbours of the vertex `x` in a chain `0, 1, …, s - 1`. -/
private theorem sum_range_chain (s x : ℕ) :
    ∑ i ∈ range s, (if x + 1 = i ∨ i + 1 = x then 1 else 0 : ℕ) =
      (if x + 1 < s then 1 else 0) + (if 0 < x ∧ x - 1 < s then 1 else 0) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ, ih]
    split_ifs <;> omega

/-- The vector with `a_{w_i} = 0` and `a_{u_k} = 1/2` solves the log discrepancy equations of the
chain `w` with two forks of weight-two arms `u`; this needs no nondegeneracy of `M(Γ)`. -/
private theorem isLogDiscrepancyVector_of_two_forks {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {s : ℕ} (hs : 0 < s) {w : Fin s → V} {u : Fin 4 → V}
    (hbij : Function.Bijective (Sum.elim w u)) (hp : ∀ v, Γ.genus v = 0)
    (hβ : ∀ v, Γ.boundary v = 0) (hn : ∀ k, Γ.weight (u k) = 2)
    (hww : ∀ i j : Fin s,
      Γ.edgeWeight (w i) (w j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0)
    (hwu : ∀ (i : Fin s) (k : Fin 4), Γ.edgeWeight (w i) (u k) =
      if ((k : ℕ) < 2 ∧ (i : ℕ) = 0) ∨ (2 ≤ (k : ℕ) ∧ (i : ℕ) + 1 = s) then 1 else 0)
    (huu : ∀ k l : Fin 4, Γ.edgeWeight (u k) (u l) = 0) {b : V → ℚ}
    (hbw : ∀ i, b (w i) = 0) (hbu : ∀ k, b (u k) = 1 / 2) :
    Γ.IsLogDiscrepancyVector b := by
  intro j
  have hui : Function.Injective u := hbij.1.comp Sum.inr_injective
  have hwu' : ∀ i k, w i ≠ u k := fun i k h => Sum.inl_ne_inr (hbij.1 h)
  have hsum : ∀ f : V → ℚ, ∑ v, f v = ∑ i, f (w i) + ∑ k, f (u k) := fun f => by
    rw [← hbij.sum_comp, Fintype.sum_sum_type]
    rfl
  have hW : ∀ y, ∑ i, b (w i) * (Γ.matrix (w i) y : ℚ) = 0 := fun y => by simp [hbw]
  obtain ⟨x | x, rfl⟩ := hbij.2 j
  · simp only [Sum.elim_inl]
    have hA : ∑ i, Γ.edgeWeight (w x) (w i) =
        (if (x : ℕ) + 1 < s then 1 else 0) + (if 0 < (x : ℕ) ∧ (x : ℕ) - 1 < s then 1 else 0) := by
      simp only [hww]
      rw [Fin.sum_univ_eq_sum_range (fun i => if (x : ℕ) + 1 = i ∨ i + 1 = (x : ℕ) then 1 else 0) s,
        sum_range_chain]
    have hB : ∑ k, Γ.edgeWeight (w x) (u k) =
        2 * (if (x : ℕ) = 0 then 1 else 0) + 2 * (if (x : ℕ) + 1 = s then 1 else 0) := by
      simp only [hwu, Fin.sum_univ_four]
      simp
      split_ifs <;> omega
    have hL : ∑ k, b (u k) * (Γ.matrix (u k) (w x) : ℚ) =
        1 / 2 * ((∑ k, Γ.edgeWeight (w x) (u k) : ℕ) : ℚ) := by
      rw [Nat.cast_sum, Finset.mul_sum]
      refine sum_congr rfl fun k _ => ?_
      simp [matrix, hbu, (hwu' x k).symm, Γ.edgeWeight_symm (u k)]
    rw [MMP.Flips.Proof_lem_fa3_four_arm_lc_if.c_eq, hsum, hsum, hW, hL, hp, hβ, ← Nat.cast_sum,
      ← Nat.cast_sum, hA, hB]
    have := x.2
    split_ifs <;> first | omega | (push_cast; norm_num)
  · simp only [Sum.elim_inr]
    have hA : ∑ i, Γ.edgeWeight (u x) (w i) = 1 := by
      simp only [Γ.edgeWeight_symm (u x), hwu]
      rw [Fin.sum_univ_eq_sum_range (fun i => if ((x : ℕ) < 2 ∧ i = 0) ∨ (2 ≤ (x : ℕ) ∧ i + 1 = s)
        then 1 else 0) s]
      by_cases hx : (x : ℕ) < 2
      · simp [hx, not_le.mpr hx, hs]
      · simp only [hx, false_and, false_or, not_lt.mp hx, true_and, sum_ite_eq_of_mem]
        rw [sum_eq_single (s - 1) (fun i _ hi => by simp; omega) (by simp; omega)]
        simp; omega
    have hL : ∑ k, b (u k) * (Γ.matrix (u k) (u x) : ℚ) = -1 := by
      rw [sum_eq_single x (fun k _ hk => by simp [matrix, hui.ne hk, huu]) (by simp)]
      simp [matrix, hbu, hn]
    rw [MMP.Flips.Proof_lem_fa3_four_arm_lc_if.c_eq, hsum, hsum, hW, hL, hp, hβ, ← Nat.cast_sum,
      ← Nat.cast_sum, hA]
    simp [huu]
    norm_num

end MMP.Flips.Proof_lem_fa3_two_fork_lc_if

namespace MMP.Flips.WeightedGraph

open MMP.Flips MMP.Flips.WeightedGraph Finset MMP.Flips.Proof_lem_fa3_two_fork_lc_if in
/-- Let `Γ` be a weighted graph with all genera and boundary degrees `0`, consisting of a chain
`w 0, …, w (s - 1)` with `2 ≤ s` and four vertices `u 0, …, u 3` of weight `2`, where `u 0` and
`u 1` are joined to `w 0`, `u 2` and `u 3` are joined to `w (s - 1)`, consecutive `w i` are
joined, all by simple edges, and there are no other edges. If `Δ(Γ) ≠ 0` (in particular if `Γ`
is negative definite), then the log discrepancy vector of `Γ` is `0` at each `w i` and `1/2` at
each `u k`. -/
@[mmp "lem_fa3_two_fork_lc_if"]
public theorem isLogDiscrepancyVector_iff_of_two_forks {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} {s : ℕ} (hs : 2 ≤ s) {w : Fin s → V}
    {u : Fin 4 → V} (hbij : Function.Bijective (Sum.elim w u))
    (hp : ∀ v, Γ.genus v = 0) (hβ : ∀ v, Γ.boundary v = 0)
    (hn : ∀ k, Γ.weight (u k) = 2)
    (hww : ∀ i j : Fin s,
      Γ.edgeWeight (w i) (w j) = if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then 1 else 0)
    (hwu : ∀ (i : Fin s) (k : Fin 4), Γ.edgeWeight (w i) (u k) =
      if ((k : ℕ) < 2 ∧ (i : ℕ) = 0) ∨ (2 ≤ (k : ℕ) ∧ (i : ℕ) + 1 = s) then 1 else 0)
    (huu : ∀ k l : Fin 4, Γ.edgeWeight (u k) (u l) = 0) (hdet : Γ.det ≠ 0) {a : V → ℚ} :
    Γ.IsLogDiscrepancyVector a ↔ (∀ i, a (w i) = 0) ∧ ∀ k, a (u k) = 1 / 2 := by
  have hwu' : ∀ i k, w i ≠ u k := fun i k h => Sum.inl_ne_inr (hbij.1 h)
  have hb : Γ.IsLogDiscrepancyVector fun v => if v ∈ Set.range u then 1 / 2 else 0 :=
    isLogDiscrepancyVector_of_two_forks (by omega) hbij hp hβ hn hww hwu huu
      (fun i => by simp [fun k => (hwu' i k).symm]) (fun k => by simp)
  refine ⟨fun ha => ?_, fun ⟨haw, hau⟩ =>
    isLogDiscrepancyVector_of_two_forks (by omega) hbij hp hβ hn hww hwu huu haw hau⟩
  obtain rfl := (existsUnique_isLogDiscrepancyVector Γ hdet).unique ha hb
  exact ⟨fun i => by simp [fun k => (hwu' i k).symm], fun k => by simp⟩

end MMP.Flips.WeightedGraph

/-!
## The log discrepancy equation at a leaf

Let `Γ` be a weighted graph and `a` a log discrepancy vector of `Γ`. If `v_j` is a vertex of
genus `p_j = 0` and boundary degree `β_j = 0` whose only neighbour `v_{j'}` is joined to it by a
simple edge, then `c_j(Γ) = 2 - 1 = 1`, and the `j`-th defining equation of `a` reads
`a_{j'} - n_j a_j = -1`.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.sub_weight_mul_eq_neg_one`: the relation
  `a_{j'} - n_j a_j = -1` at such a leaf `v_j`.

#### Implementation notes

The source states the relation for the log discrepancy vector `a(Γ)` of a negative definite
`Γ`, which exists and is unique by
`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`. The relation is the `j`-th
defining equation itself, so it is stated here for every log discrepancy vector of every
weighted graph; for negative definite `Γ` this is exactly the source's statement.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], proof of
  (3.1.13)
-/

namespace MMP.Flips.Proof_lem_fa3_leaf_relation

open MMP.Flips Finset

/-- At a vertex `v_j` whose only neighbour is `v_{j'}`, joined by a simple edge, the edge weights
out of `v_j` are the indicator of `j'`. -/
private lemma edgeWeight_eq_ite {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}
    {j j' : V} (hnbr : Γ.neighbors j = {j'}) (hedge : Γ.IsSimpleEdge j j') (k : V) :
    Γ.edgeWeight j k = if k = j' then 1 else 0 := by
  split_ifs with hk
  · exact hk ▸ hedge.2
  · obtain rfl | hkj := eq_or_ne k j
    · exact Γ.edgeWeight_self k
    · have : k ∉ Γ.neighbors j := by simp [hnbr, hk]
      simpa [WeightedGraph.neighbors, hkj] using this

end MMP.Flips.Proof_lem_fa3_leaf_relation

namespace MMP.Flips.WeightedGraph

open MMP.Flips Finset MMP.Flips.Proof_lem_fa3_leaf_relation in
/-- At a vertex `v_j` with `p_j = 0`, `β_j = 0` and a single neighbour `v_{j'}`, joined to it by a
simple edge, a log discrepancy vector `a` of `Γ` satisfies `a_{j'} - n_j a_j = -1`. -/
@[mmp "lem_fa3_leaf_relation"]
public theorem IsLogDiscrepancyVector.sub_weight_mul_eq_neg_one {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    {j j' : V} (hgenus : Γ.genus j = 0) (hboundary : Γ.boundary j = 0)
    (hnbr : Γ.neighbors j = {j'}) (hedge : Γ.IsSimpleEdge j j') :
    a j' - Γ.weight j * a j = -1 := by
  have hm := edgeWeight_eq_ite hnbr hedge
  have h := ha j
  simp only [WeightedGraph.c, WeightedGraph.matrix, Matrix.of_apply, hgenus, hboundary,
    hm] at h
  simp_rw [Γ.edgeWeight_symm _ j, hm] at h
  simp [apply_ite (Int.cast : ℤ → ℚ), mul_ite, Finset.sum_ite, Finset.filter_ne',
    Finset.filter_eq', hedge.1.symm] at h
  linarith

end MMP.Flips.WeightedGraph

/-!
## The log discrepancy relation at an interior vertex of a chain

Let `v_j` be a vertex of a weighted graph `Γ` with `p_j = 0`, `β_j = 0` and exactly two
neighbours `v_{j-1}, v_{j+1}`, each joined to `v_j` by a simple edge. Then `c_j(Γ) = 0`, and the
`j`-th defining equation of a log discrepancy vector `a` reads `a_{j-1} - n_j a_j + a_{j+1} = 0`.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.sub_weight_mul_add_eq_zero`: the relation
  `a_{j-1} - n_j a_j + a_{j+1} = 0` at such a vertex.

#### Implementation notes

The source states the relation for the log discrepancy vector `a(Γ)` of a negative definite
graph `Γ`, which is the unique log discrepancy vector of `Γ`
(`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`). The relation holds for every
log discrepancy vector of every weighted graph, and is stated so.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.12)
-/

namespace MMP.Flips.Proof_lem_fa3_chain_interior_relation

open Finset MMP.Flips

/-- At a vertex `v_j` whose neighbours are exactly `u ≠ w`, both joined by simple edges, the edge
weights out of `v_j` are the indicator of `{u, w}`. -/
private lemma edgeWeight_eq_ite {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}
    {j u w : V} (huw : u ≠ w) (hN : Γ.neighbors j = {u, w}) (hu : Γ.IsSimpleEdge j u)
    (hw : Γ.IsSimpleEdge j w) (k : V) :
    (Γ.edgeWeight j k : ℚ) = (if k = u then 1 else 0) + (if k = w then 1 else 0) := by
  obtain rfl | hku := eq_or_ne k u
  · simp [hu.2, huw]
  obtain rfl | hkw := eq_or_ne k w
  · simp [hw.2, hku]
  obtain rfl | hkj := eq_or_ne k j
  · simp [Γ.edgeWeight_self, hku, hkw]
  have : k ∉ Γ.neighbors j := by simp [hN, hku, hkw]
  simpa [WeightedGraph.neighbors, hkj, hku, hkw] using this

end MMP.Flips.Proof_lem_fa3_chain_interior_relation

namespace MMP.Flips.WeightedGraph

open Finset MMP.Flips MMP.Flips.Proof_lem_fa3_chain_interior_relation in
/-- At a vertex `j` with `p_j = 0`, `β_j = 0` and exactly two neighbours `u, w`, both joined to
`j` by simple edges, a log discrepancy vector `a` of `Γ` satisfies
`a_u - n_j a_j + a_w = 0`. -/
@[mmp "lem_fa3_chain_interior_relation"]
public theorem IsLogDiscrepancyVector.sub_weight_mul_add_eq_zero {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    {j u w : V} (hp : Γ.genus j = 0) (hβ : Γ.boundary j = 0) (huw : u ≠ w)
    (hN : Γ.neighbors j = {u, w}) (hu : Γ.IsSimpleEdge j u) (hw : Γ.IsSimpleEdge j w) :
    a u - Γ.weight j * a j + a w = 0 := by
  have hm := edgeWeight_eq_ite huw hN hu hw
  have h := ha j
  simp only [WeightedGraph.c, WeightedGraph.matrix, Matrix.of_apply, hp, hβ] at h
  simp_rw [Γ.edgeWeight_symm _ j] at h
  simp [apply_ite (Int.cast : ℤ → ℚ), hm, mul_ite, ite_mul, sum_ite, filter_ne', filter_eq',
    hu.1.symm, hw.1.symm, huw, mul_add, sum_add_distrib, add_mul] at h
  linarith

end MMP.Flips.WeightedGraph

/-!
## Concavity of the log discrepancy at a nonpositive interior vertex of a chain

Let `v_j` be a vertex of a weighted graph `Γ` with `p_j = 0`, `β_j = 0`, weight `n_j ≥ 2` and
exactly two neighbours `v_{j-1}, v_{j+1}`, each joined to `v_j` by a simple edge. For a log
discrepancy vector `a` of `Γ`, the relation `a_{j-1} + a_{j+1} = n_j a_j` shows that if
`a_j ≤ 0` then `a_{j-1} + a_{j+1} ≤ 2 a_j`.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.add_le_two_mul`: the inequality
  `a_{j-1} + a_{j+1} ≤ 2 a_j` at such a vertex when `a_j ≤ 0`.

#### Implementation notes

The source states the inequality for the log discrepancy vector `a(Γ)` of a negative definite
graph `Γ`. Here `a(Γ)` is any `a` with `Γ.IsLogDiscrepancyVector a`, which for negative definite
`Γ` is unique (`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`), and negative
definiteness is the hypothesis `Γ.IsNegDef`.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.12)
-/

namespace MMP.Flips.WeightedGraph

open MMP.Flips MMP.Flips.WeightedGraph in
/-- At a vertex `j` with `p_j = 0`, `β_j = 0`, weight `n_j ≥ 2` and exactly two neighbours
`u, w`, both joined to `j` by simple edges, the log discrepancy vector `a` of a negative
definite `Γ` with `a_j ≤ 0` satisfies `a_u + a_w ≤ 2 a_j`. -/
@[mmp "lem_fa3_chain_concave_at_nonpos"]
public theorem IsLogDiscrepancyVector.add_le_two_mul {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsNegDef) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a)
    {j u w : V} (hp : Γ.genus j = 0) (hβ : Γ.boundary j = 0) (huw : u ≠ w)
    (hN : Γ.neighbors j = {u, w}) (hu : Γ.IsSimpleEdge j u) (hw : Γ.IsSimpleEdge j w)
    (hn : 2 ≤ Γ.weight j) (haj : a j ≤ 0) :
    a u + a w ≤ 2 * a j := by
  have h := ha.sub_weight_mul_add_eq_zero hp hβ huw hN hu hw
  have hn' : (2 : ℚ) ≤ Γ.weight j := by exact_mod_cast hn
  nlinarith

end MMP.Flips.WeightedGraph

/-!
## A nonpositive log discrepancy on a subchain is bounded below by an end

Let `Γ` be a negative definite weighted graph with log discrepancy vector `a = a(Γ)`, and let
`u₀, u₁, …, u_{s+1}` (`s ≥ 1`) be distinct vertices, consecutive ones joined by simple edges,
such that every interior vertex `u_t` (`1 ≤ t ≤ s`) has genus `0`, boundary degree `0`,
weight `≥ 2` and no neighbours besides `u_{t-1}` and `u_{t+1}`. At such a vertex the relation
`a_{u_{t-1}} - n_{u_t} a_{u_t} + a_{u_{t+1}} = 0` makes `a` concave wherever it is nonpositive,
so a nonpositive value `a_{u_i}` at an interior vertex is at least `min (a_{u₀}) (a_{u_{s+1}})`.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.min_le_of_nonpos`: if `a_{u_i} ≤ 0` at an
  interior vertex of such a subchain, then `min (a_{u₀}) (a_{u_{s+1}}) ≤ a_{u_i}`.

#### Implementation notes

The subchain is an injective map `u : Fin (s + 2) → V`. Interior indices are `t + 1` for
`t : Fin s`, written `t.castSucc.succ`; their neighbours along the chain are
`t.castSucc.castSucc` and `t.succ.succ`. The vector `a(Γ)` is given as a log discrepancy vector
`a` of the negative definite graph `Γ`, which determines it
(`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`).

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.1.13)
-/

namespace MMP.Flips.Proof_lem_fa3_subchain_end_attains_nonpos

open MMP.Flips.WeightedGraph MMP.Flips

/-- Discrete minimum principle: if `f₀, …, f_{s+1}` satisfies `f_{t-1} + f_{t+1} ≤ 2 f_t` at
every interior index where `f_t ≤ 0`, then every nonpositive interior value is at least
`min f₀ f_{s+1}`. -/
private lemma min_le_of_add_le_two_mul {s : ℕ} (f : Fin (s + 2) → ℚ)
    (hf : ∀ t : Fin s, f t.castSucc.succ ≤ 0 →
      f t.castSucc.castSucc + f t.succ.succ ≤ 2 * f t.castSucc.succ)
    {i : Fin s} (hi : f i.castSucc.succ ≤ 0) :
    min (f 0) (f (Fin.last (s + 1))) ≤ f i.castSucc.succ := by
  by_contra hcon
  rw [not_le, lt_min_iff] at hcon
  obtain ⟨t₀, -, hmin⟩ := Finset.exists_min_image Finset.univ f Finset.univ_nonempty
  have hS : ({t | f t = f t₀} : Finset (Fin (s + 2))).Nonempty := ⟨t₀, by simp⟩
  obtain ⟨t, ht, hfirst⟩ : ∃ t, f t = f t₀ ∧ ∀ r < t, f t₀ < f r :=
    ⟨_, (Finset.mem_filter.mp (Finset.min'_mem _ hS)).2, fun r hr =>
      (hmin r (by simp)).lt_of_ne fun h =>
      hr.not_ge (Finset.min'_le _ _ (by simp [h]))⟩
  have hi' := hmin (i.castSucc.succ) (by simp)
  obtain ⟨t₁, rfl⟩ := Fin.exists_succ_eq.mpr (show t ≠ 0 by rintro rfl; linarith)
  obtain ⟨t₂, rfl⟩ := Fin.exists_castSucc_eq.mpr
    (show t₁ ≠ Fin.last s by rintro rfl; rw [Fin.succ_last] at ht; linarith)
  have := hf t₂ (by linarith)
  have := hfirst t₂.castSucc.castSucc (by simp [Fin.lt_def])
  have := hmin t₂.succ.succ (by simp)
  linarith

/-- A simple edge from `j` to `k` makes `k` a neighbour of `j`. -/
private lemma mem_neighbors_of_isSimpleEdge {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {j k : V} (h : Γ.IsSimpleEdge j k) : k ∈ Γ.neighbors j := by
  simp [WeightedGraph.neighbors, Ne.symm h.1, h.2]

/-- Simple edges are symmetric. -/
private lemma isSimpleEdge_symm {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {j k : V} (h : Γ.IsSimpleEdge j k) : Γ.IsSimpleEdge k j :=
  ⟨Ne.symm h.1, Γ.edgeWeight_symm k j ▸ h.2⟩

end MMP.Flips.Proof_lem_fa3_subchain_end_attains_nonpos

namespace MMP.Flips.WeightedGraph

open MMP.Flips.WeightedGraph MMP.Flips MMP.Flips.Proof_lem_fa3_subchain_end_attains_nonpos in
/-- On a subchain `u₀, …, u_{s+1}` of a negative definite weighted graph whose interior vertices
have genus `0`, boundary degree `0`, weight `≥ 2` and no neighbours off the chain, a nonpositive
value of the log discrepancy vector `a` at an interior vertex is at least the smaller of its
values at the two ends. -/
@[mmp "lem_fa3_subchain_end_attains_nonpos"]
public theorem IsLogDiscrepancyVector.min_le_of_nonpos {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} (hΓ : Γ.IsNegDef) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a)
    {s : ℕ} {u : Fin (s + 2) → V} (hu : Function.Injective u)
    (hedge : ∀ t : Fin (s + 1), Γ.IsSimpleEdge (u t.castSucc) (u t.succ))
    (hp : ∀ t : Fin s, Γ.genus (u t.castSucc.succ) = 0)
    (hβ : ∀ t : Fin s, Γ.boundary (u t.castSucc.succ) = 0)
    (hn : ∀ t : Fin s, 2 ≤ Γ.weight (u t.castSucc.succ))
    (hN : ∀ t : Fin s, Γ.neighbors (u t.castSucc.succ) ⊆ {u t.castSucc.castSucc, u t.succ.succ})
    {i : Fin s} (hai : a (u i.castSucc.succ) ≤ 0) :
    min (a (u 0)) (a (u (Fin.last (s + 1)))) ≤ a (u i.castSucc.succ) := by
  refine min_le_of_add_le_two_mul (a ∘ u) (fun t ht => ?_) hai
  have e₁ := isSimpleEdge_symm (hedge t.castSucc)
  have e₂ := Fin.succ_castSucc t ▸ hedge t.succ
  refine ha.add_le_two_mul hΓ (hp t) (hβ t) (hu.ne (by simp [Fin.ext_iff]; omega))
    ((hN t).antisymm ?_) e₁ e₂ (hn t) ht
  simp [Finset.insert_subset_iff, mem_neighbors_of_isSimpleEdge e₁,
    mem_neighbors_of_isSimpleEdge e₂]

end MMP.Flips.WeightedGraph

/-!
## The degree identity for log discrepancies of a tree

Let `Γ` be a negative definite weighted graph with simple edges and all genera `p_j = 0`,
whose underlying graph is a tree, and let `a = a(Γ)` be its log discrepancy vector. Summing
the defining equations `∑_k a_k M(Γ)_{kj} = -c_j(Γ)` over `j`, the left side becomes
`∑_k a_k (deg(v_k) - n_k)`, and the right side is `-∑_j (2 - β_j - deg(v_j))`, which equals
`∑_j β_j - 2` because a tree on `N` vertices has `N - 1` edges. Hence
`∑_k a_k (deg(v_k) - n_k) = ∑_k β_k - 2`.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.sum_mul_degree_sub_weight_eq_of_isTree`:
  the identity `∑_k a_k (deg(v_k) - n_k) = ∑_k β_k - 2`.

#### Implementation notes

The vector `a(Γ)` is not a separate definition: the statement is about any `a` with
`Γ.IsLogDiscrepancyVector a`, which for negative definite `Γ` is unique
(`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`). The hypothesis `N ≥ 1` is
part of `Γ.IsTree`, since a tree is connected and hence nonempty.

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], 3.1.10
-/

namespace MMP.Flips.Proof_lem_fa3_tree_degree_identity

open MMP.Flips Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}

/-- With simple edges, the edge weights out of `v_j` sum to `deg(v_j)`. -/
private lemma sum_erase_edgeWeight_eq_degree (hsimple : ∀ j k, Γ.edgeWeight j k ≤ 1) (j : V) :
    ∑ k ∈ univ.erase j, (Γ.edgeWeight j k : ℚ) = Γ.degree j := by
  rw [WeightedGraph.degree, card_eq_sum_ones, Nat.cast_sum, sum_filter,
    ← sum_erase univ (a := j) (by simp)]
  refine sum_congr rfl fun k hk => ?_
  have := hsimple j k
  interval_cases h : Γ.edgeWeight j k <;> simp [h, ne_of_mem_erase hk]

/-- The row sums of `M(Γ)` are `deg(v_k) - n_k` when all edges are simple. -/
private lemma sum_matrix_eq (hsimple : ∀ j k, Γ.edgeWeight j k ≤ 1) (k : V) :
    ∑ j, (Γ.matrix k j : ℚ) = (Γ.degree k : ℚ) - Γ.weight k := by
  rw [← add_sum_erase _ _ (mem_univ k), ← sum_erase_edgeWeight_eq_degree hsimple k]
  have : ∀ j ∈ univ.erase k, (Γ.matrix k j : ℚ) = Γ.edgeWeight k j := by
    intro j hj
    simp [WeightedGraph.matrix, (ne_of_mem_erase hj).symm]
  rw [sum_congr rfl this]
  simp [WeightedGraph.matrix]
  ring

/-- A tree on `N` vertices has degree sum `2(N - 1)`. -/
private lemma sum_degree_of_isTree (htree : Γ.IsTree) :
    ∑ j, (Γ.degree j : ℚ) = 2 * (Fintype.card V - 1) := by
  simp_rw [WeightedGraph.degree_eq_underlyingGraph_degree]
  rw [← Nat.cast_sum, SimpleGraph.sum_degrees_eq_twice_card_edges,
    ← (htree : Γ.underlyingGraph.IsTree).card_edgeFinset]
  push_cast
  ring

/-- For a tree with simple edges and all genera zero, `∑_j c_j(Γ) = 2 - ∑_j β_j`. -/
private lemma sum_c_of_isTree (hgenus : ∀ j, Γ.genus j = 0)
    (hsimple : ∀ j k, Γ.edgeWeight j k ≤ 1) (htree : Γ.IsTree) :
    ∑ j, Γ.c j = 2 - ∑ j, Γ.boundary j := by
  simp only [WeightedGraph.c, hgenus, sum_erase_edgeWeight_eq_degree hsimple, sum_sub_distrib,
    sum_degree_of_isTree htree, sum_const, card_univ, nsmul_eq_mul]
  push_cast
  ring

end MMP.Flips.Proof_lem_fa3_tree_degree_identity

namespace MMP.Flips.WeightedGraph

open MMP.Flips Finset MMP.Flips.Proof_lem_fa3_tree_degree_identity in
/-- For a negative definite weighted graph `Γ` with simple edges, all genera zero and
underlying graph a tree, its log discrepancy vector `a` satisfies
`∑_k a_k (deg(v_k) - n_k) = ∑_k β_k - 2`. -/
@[mmp "lem_fa3_tree_degree_identity"]
public theorem IsLogDiscrepancyVector.sum_mul_degree_sub_weight_eq_of_isTree {V : Type*}
    [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} (hgenus : ∀ j, Γ.genus j = 0)
    (hsimple : ∀ j k, Γ.edgeWeight j k ≤ 1) (htree : Γ.IsTree) (hneg : Γ.IsNegDef)
    {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    ∑ k, a k * ((Γ.degree k : ℚ) - Γ.weight k) = ∑ k, Γ.boundary k - 2 := by
  simp_rw [← sum_matrix_eq hsimple, mul_sum]
  rw [sum_comm, sum_congr rfl fun j _ => ha j, sum_neg_distrib,
    sum_c_of_isTree hgenus hsimple htree]
  ring

end MMP.Flips.WeightedGraph

/-!
## Nonnegativity of log discrepancies of a rational tree

Let `Γ` be a negative definite rational tree and `a(Γ)` its log discrepancy vector. Call a
vertex `v_j` *special* if `deg(v_j) ≥ 3` or `β_j > 0`. Then all entries of `a(Γ)` are
nonnegative as soon as the entries at the special vertices are: a negative minimum of `a(Γ)`
would be attained at a non-special vertex, and along the chains of non-special vertices of
degree at most `2` the log discrepancy equations push the minimum out to a special vertex or a
leaf, where it cannot be negative.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.forall_nonneg_iff_of_isRationalTree`: for a
  negative definite rational tree `Γ`, `a(Γ)_j ≥ 0` for all `j` if and only if `a(Γ)_j ≥ 0`
  for all `j` with `deg(v_j) ≥ 3` or `β_j > 0`.

#### Implementation notes

The vector `a(Γ)` is not a separate definition: the statement is about any `a` with
`Γ.IsLogDiscrepancyVector a`, which for negative definite `Γ` is unique
(`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`).

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Lemma 3.1.13
-/

namespace MMP.Flips.Proof_lem_fa3_tree_nonneg_criterion

open MMP.Flips Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {Γ : WeightedGraph V}

/-- On a rational tree the edge weights out of `v_j` are the indicator of its neighbours. -/
private lemma edgeWeight_cast_eq_ite (hΓ : Γ.IsRationalTree) (j k : V) :
    (Γ.edgeWeight j k : ℚ) = if k ∈ Γ.neighbors j then 1 else 0 := by
  have h1 := hΓ.edgeWeight_le_one j k
  by_cases hk : k = j
  · subst hk; simp [WeightedGraph.neighbors, Γ.edgeWeight_self]
  · by_cases h0 : Γ.edgeWeight j k = 0
    · simp [WeightedGraph.neighbors, h0]
    · have : Γ.edgeWeight j k = 1 := by omega
      simp [WeightedGraph.neighbors, this, hk]

/-- The `j`-th log discrepancy equation on a rational tree:
`∑_{k ∼ j} a_k = n_j a_j - 2 + β_j + deg(v_j)`. -/
private lemma eq_of_isRationalTree (hΓ : Γ.IsRationalTree) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) (j : V) :
    ∑ k ∈ Γ.neighbors j, a k =
      Γ.weight j * a j - 2 + Γ.boundary j + (Γ.neighbors j).card := by
  have h := ha j
  have hjN : j ∉ Γ.neighbors j := by simp [WeightedGraph.neighbors]
  have hNe : univ.erase j ∩ Γ.neighbors j = Γ.neighbors j := by
    ext k; by_cases hk : k = j <;> simp [hk, hjN]
  have hc : ∑ k ∈ univ.erase j, (Γ.edgeWeight j k : ℚ) = (Γ.neighbors j).card := by
    simp_rw [edgeWeight_cast_eq_ite hΓ, sum_ite_mem, hNe, sum_const, nsmul_one]
  have hs : ∑ k, a k * (Γ.matrix k j : ℚ) =
      -Γ.weight j * a j + ∑ k ∈ Γ.neighbors j, a k := by
    rw [← add_sum_erase _ _ (mem_univ j)]
    congr 1
    · simp [WeightedGraph.matrix]; ring
    · rw [← hNe, ← sum_ite_mem]
      refine sum_congr rfl fun k hk => ?_
      have hkj : k ≠ j := ne_of_mem_erase hk
      simp only [WeightedGraph.matrix, Matrix.of_apply, if_neg hkj]
      rw [Int.cast_natCast, Γ.edgeWeight_symm, edgeWeight_cast_eq_ite hΓ]
      split_ifs <;> simp
  rw [hs, WeightedGraph.c, hc, hΓ.genus_eq_zero j] at h
  push_cast at h
  linarith

/-- At a vertex `x` of degree at most `2` and boundary degree `0` where `a` attains a
nonpositive minimum, `x` has exactly two neighbours, and `a` attains the minimum at both. -/
private lemma card_neighbors_eq_two_of_isMin (hΓ : Γ.IsRationalTree) {a : V → ℚ}
    (ha : Γ.IsLogDiscrepancyVector a) {x : V} (hmin : ∀ y, a x ≤ a y) (hneg : a x ≤ 0)
    (hdeg : (Γ.neighbors x).card ≤ 2) (hβ0 : Γ.boundary x = 0) :
    (Γ.neighbors x).card = 2 ∧ ∀ y ∈ Γ.neighbors x, a y = a x := by
  have h := eq_of_isRationalTree hΓ ha x
  rw [hβ0] at h
  have hn : (2 : ℚ) ≤ Γ.weight x := by exact_mod_cast hΓ.two_le_weight x
  have hsum : ∑ y ∈ Γ.neighbors x, (a y - a x) =
      (Γ.weight x - (Γ.neighbors x).card) * a x - 2 + (Γ.neighbors x).card := by
    rw [sum_sub_distrib, h, sum_const, nsmul_eq_mul]; ring
  have hnn : ∀ y ∈ Γ.neighbors x, 0 ≤ a y - a x := fun y _ => sub_nonneg.mpr (hmin y)
  have hpos := sum_nonneg hnn
  have hcard : (Γ.neighbors x).card = 2 := by
    by_contra hne
    have hle : ((Γ.neighbors x).card : ℚ) ≤ 1 := by exact_mod_cast (by omega : _ ≤ 1)
    nlinarith
  refine ⟨hcard, fun y hy => ?_⟩
  rw [hcard] at hsum
  push_cast at hsum
  have hz : ∑ y ∈ Γ.neighbors x, (a y - a x) = 0 := le_antisymm (by nlinarith) hpos
  linarith [(sum_eq_zero_iff_of_nonneg hnn).mp hz y hy]

/-- On a rational tree, a function `a` cannot attain its minimum `a x` only at vertices with
exactly two neighbours, all of them again at the minimum: the minimum would propagate along the
connected tree to every vertex, making every vertex of degree two, while a nontrivial finite
tree has a leaf. -/
private lemma false_of_forall_isMin (hΓ : Γ.IsRationalTree) {a : V → ℚ} (x : V)
    (key : ∀ y, a y = a x → (Γ.neighbors y).card = 2 ∧ ∀ z ∈ Γ.neighbors y, a z = a x) :
    False := by
  have htree : Γ.underlyingGraph.IsTree :=
    hΓ.isTree_or_isEmpty.resolve_right fun h => h.false x
  have hwalk : ∀ {u v : V} (p : Γ.underlyingGraph.Walk u v), a u = a x → a v = a x := by
    intro u v p
    induction p with
    | nil => exact id
    | cons hadj _ ih => exact fun hu => ih ((key _ hu).2 _ (Γ.mem_neighbors.mpr hadj))
  have hdeg (y : V) : Γ.underlyingGraph.degree y = 2 := by
    rw [← Γ.degree_eq_underlyingGraph_degree]
    exact (key y (hwalk (htree.connected.preconnected x y).some rfl)).1
  have : Nontrivial V := SimpleGraph.nontrivial_of_degree_ne_zero (hdeg x ▸ two_ne_zero)
  obtain ⟨v, hv⟩ := htree.exists_vert_degree_one_of_nontrivial
  exact absurd (hv.symm.trans (hdeg v)) (by decide)

end MMP.Flips.Proof_lem_fa3_tree_nonneg_criterion

namespace MMP.Flips.WeightedGraph

open MMP.Flips Finset MMP.Flips.Proof_lem_fa3_tree_nonneg_criterion in
/-- For a negative definite rational tree `Γ` with log discrepancy vector `a`, every `a j` is
nonnegative if and only if `a j` is nonnegative at every vertex `j` of degree at least `3` and
at every vertex with positive boundary degree `β_j`. -/
@[mmp "lem_fa3_tree_nonneg_criterion"]
public theorem IsLogDiscrepancyVector.forall_nonneg_iff_of_isRationalTree {V : Type*}
    [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    (∀ j, 0 ≤ a j) ↔ ∀ j, 3 ≤ Γ.degree j ∨ 0 < Γ.boundary j → 0 ≤ a j := by
  refine ⟨fun h j _ => h j, fun hsp => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨j₀, hj₀⟩ := hcon
  haveI : Nonempty V := ⟨j₀⟩
  obtain ⟨x, -, hx⟩ := exists_min_image univ a univ_nonempty
  have hmin : ∀ y, a x ≤ a y := fun y => hx y (mem_univ y)
  have hm : a x < 0 := (hmin j₀).trans_lt hj₀
  -- every vertex at which the minimum is attained is non-special, of degree two, and has all
  -- its neighbours at the minimum
  refine false_of_forall_isMin hΓ (a := a) x fun y hy => ?_
  have hsy : ¬ (3 ≤ Γ.degree y ∨ 0 < Γ.boundary y) := fun h => by
    have := hsp y h; linarith
  push Not at hsy
  have := card_neighbors_eq_two_of_isMin hΓ ha (x := y) (hy ▸ hmin) (hy ▸ hm.le)
    (by change Γ.degree y ≤ 2; omega) (le_antisymm hsy.2 (Γ.boundary_nonneg y))
  exact ⟨this.1, fun z hz => (this.2 z hz).trans hy⟩

end MMP.Flips.WeightedGraph

/-!
## Positivity of log discrepancies of a rational tree

Let `Γ` be a negative definite rational tree and `a(Γ)` its log discrepancy vector. Call a
vertex `v_j` *special* if `deg(v_j) ≥ 3` or `β_j > 0`. Then all entries of `a(Γ)` are
positive as soon as the entries at the special vertices are: along the chains of non-special
vertices the log discrepancy equations force a nonpositive minimum out to a special vertex or
a leaf, where it cannot occur.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.forall_pos_iff_of_isRationalTree`: for a
  negative definite rational tree `Γ`, `a(Γ)_j > 0` for all `j` if and only if `a(Γ)_j > 0`
  for all `j` with `deg(v_j) ≥ 3` or `β_j > 0`.

#### Implementation notes

The vector `a(Γ)` is not a separate definition: the statement is about any `a` with
`Γ.IsLogDiscrepancyVector a`, which for negative definite `Γ` is unique
(`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`).

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], Lemma 3.1.13
-/

namespace MMP.Flips.WeightedGraph

open MMP.Flips Finset MMP.Flips.Proof_lem_fa3_tree_nonneg_criterion in
/-- For a negative definite rational tree `Γ` with log discrepancy vector `a`, every `a j` is
positive if and only if `a j` is positive at every vertex `j` of degree at least `3` and at
every vertex with positive boundary degree `β_j`. -/
@[mmp "lem_fa3_tree_pos_criterion"]
public theorem IsLogDiscrepancyVector.forall_pos_iff_of_isRationalTree {V : Type*}
    [Fintype V] [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree)
    (hneg : Γ.IsNegDef) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    (∀ j, 0 < a j) ↔ ∀ j, 3 ≤ Γ.degree j ∨ 0 < Γ.boundary j → 0 < a j := by
  refine ⟨fun h j _ => h j, fun hsp => ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨j₀, hj₀⟩ := hcon
  haveI : Nonempty V := ⟨j₀⟩
  obtain ⟨x, -, hx⟩ := exists_min_image univ a univ_nonempty
  have hmin : ∀ y, a x ≤ a y := fun y => hx y (mem_univ y)
  have hm : a x ≤ 0 := (hmin j₀).trans hj₀
  -- every vertex at which the minimum is attained is non-special, as `a` is positive at the
  -- special vertices, hence of degree two with all its neighbours at the minimum
  refine false_of_forall_isMin hΓ (a := a) x fun y hy => ?_
  rw [← hy] at hmin hm ⊢
  refine card_neighbors_eq_two_of_isMin hΓ ha hmin hm ?_
    (le_antisymm (not_lt.mp fun h => (hsp y (.inr h)).not_ge hm) (Γ.boundary_nonneg y))
  by_contra h
  exact (hsp y (.inl (by change 3 ≤ (Γ.neighbors y).card; omega))).not_ge hm

end MMP.Flips.WeightedGraph

/-!
## Nonnegativity of log discrepancies of a star-shaped rational tree

Let `Γ` be a negative definite rational tree with all boundary degrees `β_j = 0` which is a
star at the vertex `v`, its arms being chains attached to `v` at an end. Every vertex other
than `v` has degree at most `2` and no vertex has positive boundary degree, so `v` is the only
possibly special vertex of `Γ`, and the log discrepancy vector `a(Γ)` is nonnegative as soon as
its entry at `v` is.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.forall_nonneg_iff_of_isStar`: for such a
  star `Γ`, `a(Γ)_k ≥ 0` for every `k` if and only if `a(Γ)_v ≥ 0`.

#### Implementation notes

The source states the criterion for a star with three arms; the statement here allows any
number `N` of arms, the argument being the same. The vector `a(Γ)` is not a separate
definition: the statement is about any `a` with `Γ.IsLogDiscrepancyVector a`, which for
negative definite `Γ` is unique (`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`).

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.2.2)
-/

namespace MMP.Flips.Proof_lem_fa3_three_arm_criterion

open Finset MMP.Flips MMP.Flips.WeightedGraph

/-- A component `C` of `Γ - v` is closed under adjacency in `Γ` away from `v`. -/
private theorem mem_of_adj_of_isComponentOfRemoveVertex {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} {v : V} {C : Finset V}
    (hC : Γ.IsComponentOfRemoveVertex v C) {k w : V} (hk : k ∈ C) (hwv : w ≠ v)
    (hadj : Γ.underlyingGraph.Adj k w) : w ∈ C := by
  obtain ⟨c, hc⟩ := hC
  have hkC : k ∈ (C : Set V) := hk
  rw [hc] at hkC
  obtain ⟨x, hx, rfl⟩ := hkC
  let x' : ↥(univ \ {v} : Finset V) := ⟨w, by simp [hwv]⟩
  have hxx' : (Γ.removeVertex v).underlyingGraph.Adj x x' :=
    ⟨fun h => hadj.1 (congrArg Subtype.val h), hadj.2⟩
  change w ∈ (C : Set V)
  rw [hc]
  refine ⟨x', ?_, rfl⟩
  rw [SimpleGraph.ConnectedComponent.mem_supp_iff] at hx ⊢
  exact hx ▸ (SimpleGraph.ConnectedComponent.sound hxx'.reachable).symm

/-- In a weighted graph, a vertex `k` of a chain `C` attached to `v` at an end has degree at
most `2`: its neighbours other than `v` lie in `C`, hence are its two neighbours along the chain,
and `v` is adjacent only to the first vertex of the chain. -/
private theorem degree_le_two_of_isChainAttachedAtEnd {V : Type*} [Fintype V] [DecidableEq V]
    {Γ : WeightedGraph V} {v : V} {C : Finset V} (hC : Γ.IsChainAttachedAtEnd v C) {k : V}
    (hk : k ∈ C) : Γ.degree k ≤ 2 := by
  obtain ⟨-, hcomp, s, hs, e, he, -, huniq⟩ := hC
  obtain ⟨t, ht⟩ : ∃ t, (e t : V) = k := ⟨e.symm ⟨k, hk⟩, by simp⟩
  let f : ℕ → V := fun j => if h : j < s then (e ⟨j, h⟩ : V) else v
  have hf : ∀ (j : Fin s) (n : ℕ), (j : ℕ) = n → f n = e j := by
    rintro j n rfl; simp [f]
  have hsub : Γ.neighbors k ⊆ {if (t : ℕ) = 0 then v else f (t - 1), f (t + 1)} := by
    intro w hw
    rw [mem_neighbors] at hw
    by_cases hwv : w = v
    · subst hwv
      have : t = ⟨0, hs⟩ := e.injective (Subtype.ext (ht.trans (huniq k hk hw.symm)))
      simp [this]
    · obtain ⟨j, rfl⟩ : ∃ j, (e j : V) = w :=
        ⟨e.symm ⟨w, mem_of_adj_of_isComponentOfRemoveVertex hcomp hk hwv hw⟩, by simp⟩
      have hpos : 0 < (Γ.restrict C).edgeWeight (e t) (e j) := by
        change 0 < Γ.edgeWeight (e t) (e j); rw [ht]; exact hw.2
      rw [he.edgeWeight_eq t j] at hpos
      split_ifs at hpos with hcase
      · rcases hcase with h | h
        · simp [hf j _ h.symm]
        · simp [show (t : ℕ) ≠ 0 by omega, hf j (t - 1) (by omega)]
      · exact absurd hpos (lt_irrefl 0)
  calc Γ.degree k = #(Γ.neighbors k) := rfl
    _ ≤ _ := card_le_card hsub
    _ ≤ 2 := card_le_two

end MMP.Flips.Proof_lem_fa3_three_arm_criterion

namespace MMP.Flips.WeightedGraph

open Finset MMP.Flips MMP.Flips.WeightedGraph MMP.Flips.Proof_lem_fa3_three_arm_criterion in
/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which is a star
with arms `arms` at `v`, and let `a` be its log discrepancy vector. Then `a k ≥ 0` for every
vertex `k` if and only if `a v ≥ 0`. -/
@[mmp "lem_fa3_three_arm_criterion"]
public theorem IsLogDiscrepancyVector.forall_nonneg_iff_of_isStar {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {N : ℕ} {arms : Fin N → Finset V}
    (hstar : Γ.IsStar v arms) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    (∀ k, 0 ≤ a k) ↔ 0 ≤ a v := by
  refine ⟨fun h => h v, fun hv => ?_⟩
  refine (ha.forall_nonneg_iff_of_isRationalTree hΓ hneg).2 fun j hj => ?_
  rcases hj with hj | hj
  · by_cases hjv : j = v
    · exact hjv ▸ hv
    · have hmem : j ∈ univ.biUnion arms := by rw [hstar.biUnion_eq]; simp [hjv]
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 hmem
      have := degree_le_two_of_isChainAttachedAtEnd (hstar.isChainAttachedAtEnd i) hi
      omega
  · simp [hβ] at hj

end MMP.Flips.WeightedGraph

/-!
## Positivity of log discrepancies of a star-shaped rational tree

Let `Γ` be a negative definite rational tree with all boundary degrees `β_j = 0` which is a
star at the vertex `v`, its arms being chains attached to `v` at an end. Since `v` is the only
possibly special vertex of `Γ`, the log discrepancy vector `a(Γ)` is positive as soon as its
entry at `v` is. This is the strict companion of
`MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.forall_nonneg_iff_of_isStar`.

#### Main results

* `MMP.Flips.WeightedGraph.IsLogDiscrepancyVector.forall_pos_iff_of_isStar`: for such a
  star `Γ`, `a(Γ)_k > 0` for every `k` if and only if `a(Γ)_v > 0`.

#### Implementation notes

The source states the criterion for a star with three arms; the statement here allows any
number `N` of arms, the argument being the same. The vector `a(Γ)` is any `a` with
`Γ.IsLogDiscrepancyVector a`, which for negative definite `Γ` is unique
(`MMP.Flips.WeightedGraph.existsUnique_isLogDiscrepancyVector`).

#### References

* [J. Kollár et al., *Flips and abundance for algebraic threefolds*][KollarFlips], (3.2.2)
-/

namespace MMP.Flips.WeightedGraph

open Finset MMP.Flips MMP.Flips.WeightedGraph in
/-- Let `Γ` be a negative definite rational tree with all boundary degrees `0` which is a star
with arms `arms` at `v`, and let `a` be its log discrepancy vector. Then `a k > 0` for every
vertex `k` if and only if `a v > 0`. -/
@[mmp "lem_fa3_three_arm_criterion_pos"]
public theorem IsLogDiscrepancyVector.forall_pos_iff_of_isStar {V : Type*} [Fintype V]
    [DecidableEq V] {Γ : WeightedGraph V} (hΓ : Γ.IsRationalTree) (hneg : Γ.IsNegDef)
    (hβ : ∀ j, Γ.boundary j = 0) {v : V} {N : ℕ} {arms : Fin N → Finset V}
    (hstar : Γ.IsStar v arms) {a : V → ℚ} (ha : Γ.IsLogDiscrepancyVector a) :
    (∀ k, 0 < a k) ↔ 0 < a v := by
  refine ⟨fun h => h v, fun hv => ?_⟩
  refine (ha.forall_pos_iff_of_isRationalTree hΓ hneg).2 fun j hj => ?_
  rcases hj with hj | hj
  · by_cases hjv : j = v
    · exact hjv ▸ hv
    · have hmem : j ∈ univ.biUnion arms := by rw [hstar.biUnion_eq]; simp [hjv]
      obtain ⟨i, -, hi⟩ := mem_biUnion.1 hmem
      have := MMP.Flips.Proof_lem_fa3_three_arm_criterion.degree_le_two_of_isChainAttachedAtEnd
        (hstar.isChainAttachedAtEnd i) hi
      omega
  · simp [hβ] at hj

end MMP.Flips.WeightedGraph
