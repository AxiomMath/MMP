module

public import MMP.Attr
public import MMP.AlgebraicGeometry.MMP.Fourfold.ThreefoldPreparedChain
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChainAdmissibleScale
import MMP.AlgebraicGeometry.MMP.Fourfold.TerminalChain.Models
import MMP.AlgebraicGeometry.MMP.Fourfold.StabilizedTail.BadCurvesGood

/-!
# Existence of prepared chains

Let `(p_i, Θ_i)_{i ≥ 0}` be a terminal chain over a stabilized tail
`(X_i, B_i, Z_i, f_i, f_i⁺)_{i ≥ 0}`, and fix an admissible scale `N` for it. Then the tail of
the chain starting at the junction `Y_{i₀}` is a prepared chain at scale `N` for every
sufficiently large `i₀`: from some index on, every fixed label has constant coefficient equal to
its eventual value and every default is constant, every varying label has positive coefficient
at every junction, and `p_i` maps the union of the varying labels onto a finite set of closed
points.

## Main results

* `MMP.Fourfold.StabilizedTail.TerminalChain.eventually_exists_preparedChain`: for an
  admissible scale `N`, for all sufficiently large `i₀` there is a prepared chain with
  underlying terminal chain `C`, starting at `i₀`, at scale `N`.
-/

@[expose] public section

namespace MMP.Fourfold

namespace StabilizedTail

namespace TerminalChain

/-- From the index `i₁` given by `TerminalChain.exists_isCentre_closedPoint_of_isVaryingLabel` on,
a varying label has a centre on the junction `Y_i`, and `p_i` maps every centre of it onto one
closed point of `X_i`. -/
private theorem exists_isClosed_image_eq_of_isVaryingLabel {T : StabilizedTail}
    (C : TerminalChain T) :
    ∃ i₁ : ℕ, ∀ i ≥ i₁, ∀ S : C.Label, C.IsVaryingLabel S →
      ∃ x : T.X i, IsClosed ({x} : Set (T.X i)) ∧
        (∃ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P) ∧
        ∀ P : MMP.Mori.PrimeDivisor (C.model ⟨i, none⟩), C.IsLabelCentre S ⟨i, none⟩ P →
          (C.junction i).p '' P.support = {x} := by
  obtain ⟨i₁, hv⟩ := C.exists_isCentre_closedPoint_of_isVaryingLabel
  refine ⟨i₁, fun i hi S hS => ?_⟩
  obtain ⟨-, -, s', -, hE, x, hx, himg, -⟩ := hv i hi S hS
  refine ⟨x, hx, ⟨_, hE⟩, fun P hP => ?_⟩
  obtain ⟨Q, -, hQ⟩ := ((C.isKltTerminalPair_and_antitone_and_monotone.1 ⟨i, none⟩).2.2.2.2.1 S)
  rw [hQ P hP, ← hQ _ hE]
  exact himg

/-- Every terminal chain `C` over a stabilized tail has a tail which is a prepared chain: for
every admissible scale `N` of `C`, for all sufficiently large `i₀` there is a prepared chain
whose terminal chain is `C`, starting at the junction `Y_{i₀}`, at scale `N`. -/
@[mmp "lem_mmp_indexd_prepared_chain_exists"]
public theorem eventually_exists_preparedChain {T : StabilizedTail} (C : TerminalChain T)
    {N : ℕ} (hN : C.IsAdmissibleScale N) :
    ∀ᶠ i₀ in Filter.atTop,
      ∃ Q : PreparedChain T, Q.chain = C ∧ Q.start = i₀ ∧ Q.scale = N := by
  have := C.finite_label
  obtain ⟨i₀, hd, hc⟩ := C.exists_forall_ge_isLabelDefault_and_isLabelCoefficient N
  obtain ⟨i₁, hv⟩ := exists_isClosed_image_eq_of_isVaryingLabel C
  filter_upwards [Filter.eventually_ge_atTop (max i₀ i₁)] with j hj
  have hj₀ : i₀ ≤ j := (le_max_left _ _).trans hj
  have hj₁ : i₁ ≤ j := (le_max_right _ _).trans hj
  refine ⟨⟨C, j, N, hN, ?_, ?_, ?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rintro S ⟨c, n, h⟩
    exact ⟨c, ⟨n, h⟩, fun x hx => hc S c ⟨n, h⟩ x (hj₀.trans hx)⟩
  · intro i hi S hS
    obtain ⟨-, -, ⟨P, hP⟩, -⟩ := hv i (hj₁.trans hi) S hS
    exact ⟨_, ⟨P, hP, rfl⟩, hS.pos_of_isJunctionLabelCoefficient ⟨P, hP, rfl⟩⟩
  · intro i hi
    choose! x _ _ hx using hv i (hj₁.trans hi)
    refine (Set.finite_range x).subset ?_
    rintro _ ⟨y, ⟨S, hS, P, hP, hy⟩, rfl⟩
    have : (C.junction i).p y ∈ (C.junction i).p '' P.support := ⟨y, hy, rfl⟩
    rw [hx S hS P hP] at this
    exact ⟨S, this.symm⟩
  · rintro i hi _ ⟨y, ⟨S, hS, P, hP, hy⟩, rfl⟩
    obtain ⟨x, hxc, -, hx⟩ := hv i (hj₁.trans hi) S hS
    have : (C.junction i).p y ∈ (C.junction i).p '' P.support := ⟨y, hy, rfl⟩
    rw [hx P hP, Set.mem_singleton_iff] at this
    rwa [this]
  · intro S
    obtain ⟨d, hd⟩ := hd S
    exact ⟨d, fun x hx => hd x (hj₀.trans hx)⟩

end TerminalChain

end StabilizedTail

end MMP.Fourfold
