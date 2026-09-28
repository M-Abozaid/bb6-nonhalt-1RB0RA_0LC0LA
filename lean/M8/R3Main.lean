import M8.R3Cycle
namespace M8.R3
set_option maxRecDepth 1000000

/-! # Base case and the final theorem.
Blank tape -> step 46083: the pre-absorption state `(l, a) = (3, 0)` (level-4 ladder `[16,8,4,2]`,
all separators `1.`, `B1 = 2`, counter value 17), kernel-checked by `decide +kernel`. -/

def c0 : Cfg := ⟨.B, [true, false, false, true, false, false, true, false, true, true], true, [true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, false, true, true, true, false, true, true, true, true, false, false, true, true, true, false, true, true, true, true, false]⟩

theorem run_zero (c : Cfg) : run 0 c = c := rfl

theorem base_run : run 46083 init = c0 := by decide +kernel

def S0 : AS := ⟨0, .cl 17, 1, Ol 4⟩

theorem dig17 : dig 17 = [.t, .t, .o] := by
  rw [dig_pos 17 (by decide)]
  rw [show 17 / 3 = 5 from rfl, dig_pos 5 (by decide), show 5 / 3 = 1 from rfl, dig_pos 1 (by decide),
    show 1 / 3 = 0 from rfl, dig_zero]
  rfl

theorem base_pe : PE c0 (tape S0) := by
  unfold tape S0 ctape
  simp only [dig17]
  unfold PE
  decide +kernel

theorem base_inv : PreInv S0 :=
  ⟨3, 0, 17, by decide, rfl, rfl, by decide, rfl, by decide, by decide, by decide⟩

/-- **M8 = 1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_---1RA never halts from the blank tape.** -/
theorem nonhalt : ∀ n, ¬ halted (run n init) := by
  intro n
  have h := nonhalt_from (run 46083 init) S0 base_inv (base_run ▸ base_pe)
  by_cases hn : 46083 ≤ n
  · rw [show n = 46083 + (n - 46083) by omega, run_add]; exact h _
  · intro hh
    have e : run 46083 init = run n init := by
      rw [show 46083 = n + (46083 - n) by omega, run_add]; exact run_H _ _ hh
    have h0 := h 0
    rw [run_zero, e] at h0
    exact h0 hh

#print axioms nonhalt

end M8.R3
