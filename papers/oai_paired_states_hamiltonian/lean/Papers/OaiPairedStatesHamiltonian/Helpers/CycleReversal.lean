module

public import Papers.OaiPairedStatesHamiltonian.Helpers.StatesCore

/-! Reversal of oriented simple cycles, independent of pair weights. -/

@[expose] public section
namespace OaiPairedStatesHamiltonian
set_option linter.style.openClassical false
open Classical
attribute [local instance] propDecidable
variable (T : SphereMap)

-- @node: cycle_heads_nodup
/-- [The heads of the directed edges of a simple cycle contain no repeated
vertex](goal). -/
lemma cycle_heads_nodup (C : T.Cycle) : (C.val.map T.head).Nodup := by
  apply List.nodup_iff_injective_getElem.mpr
  intro i j hij
  have hi := C.property.1.2.2 ⟨i.val, by simpa using i.isLt⟩
  have hj := C.property.1.2.2 ⟨j.val, by simpa using j.isLt⟩
  simp only [List.getElem_map] at hij
  have heq := C.property.2.get_inj_iff.mp (show
      (C.val.map T.vert).get ⟨(i.val + 1) % C.val.length, by
        simpa using T.nextIndex_lt C.val ⟨i.val, by simpa using i.isLt⟩⟩ =
      (C.val.map T.vert).get ⟨(j.val + 1) % C.val.length, by
        simpa using T.nextIndex_lt C.val ⟨j.val, by simpa using j.isLt⟩⟩ from
      by simpa using hi.symm.trans (hij.trans hj))
  have he := congrArg Fin.val heq
  change (i.val + 1) % C.val.length = (j.val + 1) % C.val.length at he
  have hiLt : i.val < C.val.length := by simpa using i.isLt
  have hjLt : j.val < C.val.length := by simpa using j.isLt
  apply Fin.ext
  by_cases hiLast : i.val + 1 = C.val.length
  · rw [hiLast, Nat.mod_self] at he
    by_cases hjLast : j.val + 1 = C.val.length
    · omega
    · rw [Nat.mod_eq_of_lt (by omega)] at he
      omega
  · rw [Nat.mod_eq_of_lt (by omega)] at he
    by_cases hjLast : j.val + 1 = C.val.length
    · rw [hjLast, Nat.mod_self] at he
      omega
    · rw [Nat.mod_eq_of_lt (by omega)] at he
      omega

-- @node: reverseCycle_isSimple
/-- [Reversing the order of a simple cycle's directed edges and reversing each
edge's direction again gives a simple cycle](goal). -/
lemma reverseCycle_isSimple (C : T.Cycle) : T.IsSimpleCycle (reverseDarts T C.val) := by
  have hedge (d : T.Dart) : T.edgeOf (T.edgeInv d) = T.edgeOf d :=
    ((T.edgeOf_eq_iff d (T.edgeInv d)).mpr (Or.inr rfl)).symm
  have hhead (d : T.Dart) : T.head (T.edgeInv d) = T.vert d := by
    exact congrArg T.vert (T.edgeInv_involutive d)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · simpa [reverseDarts] using C.property.1.1
  · simpa only [reverseDarts, List.map_map, Function.comp_def, hedge,
      List.map_reverse, List.nodup_reverse] using C.property.1.2.1
  · intro i
    have hi : i.val < C.val.length := by simpa [reverseDarts] using i.isLt
    have hlen : (reverseDarts T C.val).length = C.val.length := by simp [reverseDarts]
    have hpos : 0 < C.val.length := by omega
    let j := (i.val + 1) % C.val.length
    have hj : j < C.val.length := Nat.mod_lt _ hpos
    have hstep := C.property.1.2.2
      ⟨C.val.length - 1 - j, by omega⟩
    have hindex : (C.val.length - 1 - j + 1) % C.val.length =
        C.val.length - 1 - i.val := by
      dsimp [j]
      by_cases hlast : i.val + 1 = C.val.length
      · rw [hlast, Nat.mod_self]
        have he : C.val.length - 1 - 0 + 1 = C.val.length := by omega
        rw [he, Nat.mod_self]
        omega
      · have hjEq : (i.val + 1) % C.val.length = i.val + 1 :=
          Nat.mod_eq_of_lt (by omega)
        rw [hjEq]
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    change T.head ((reverseDarts T C.val)[i.val]) =
      T.vert ((reverseDarts T C.val)[(i.val + 1) % (reverseDarts T C.val).length]'(by
        exact T.nextIndex_lt (reverseDarts T C.val) i))
    simp only [reverseDarts, List.getElem_map, List.getElem_reverse, hhead,
      List.length_map, List.length_reverse]
    change T.vert (C.val[C.val.length - 1 - i.val]) =
      T.head (C.val[C.val.length - 1 - j])
    simpa only [List.get_eq_getElem, hindex] using hstep.symm
  · have hn := cycle_heads_nodup T C
    change (C.val.map (fun d => T.vert (T.edgeInv d))).Nodup at hn
    simpa only [reverseDarts, List.map_map, Function.comp_def,
      List.map_reverse, List.nodup_reverse] using hn
/-- In [the given sphere map](hyp:T), the [reversal](goal) of [a simple
cycle](hyp:C) traverses its directed edges in reverse order and with reversed
directions. -/
noncomputable def reverseCycle (C : T.Cycle) : T.Cycle :=
  ⟨reverseDarts T C.val, reverseCycle_isSimple T C⟩


end OaiPairedStatesHamiltonian
