module

public import DosenPetric.GentzenCopiesPositions
public import DosenPetric.GentzenExchangePositions

@[expose] public section
set_option autoImplicit false
namespace DosenPetric.Reduced.Gentzen
universe u

def lengthCopy : List Nat→Nat→Nat
  | [],i => i+1
  | n::ns,i => if i<n then i else if i=n then n+ns.sum else n+lengthCopy ns (i-n-1)

theorem gap_length_sum {P : Type u} (gs : List (List (NormalForm P))) :
    (gs.map List.length).sum=(gaps gs).length := by
  induction gs with
  | nil => rfl
  | cons Γ gs ih => simp only [List.map_cons,List.sum_cons,gaps,List.length_append,ih]

theorem copyIndex_lengths {P : Type u} (gs : List (List (NormalForm P))) (i : Nat) :
    copyIndex gs i=lengthCopy (gs.map List.length) i := by
  induction gs generalizing i with
  | nil => rfl
  | cons Γ gs ih =>
    simp only [copyIndex,lengthCopy,List.map_cons,gap_length_sum]
    rw [ih]

theorem lengthCopy_three_last (a b c : Nat) :
    lengthCopy [a,b,c] (a+b+c+2)=a+b+c := by
  rw [lengthCopy,ite_eq_right (by omega : ¬a+b+c+2<a),ite_eq_right (by omega : a+b+c+2≠a)]
  have h₁ : a+b+c+2-a-1=b+c+1 := by omega
  rw [h₁,lengthCopy,ite_eq_right (by omega : ¬b+c+1<b),ite_eq_right (by omega : b+c+1≠b)]
  have h₂ : b+c+1-b-1=c := by omega
  rw [h₂,lengthCopy,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl]
  simp only [List.sum_nil,Nat.add_zero,Nat.add_assoc]

theorem lengthCopy_rotate_head (x y z t : Nat) :
    exchangeIndex (x+y+z) t 1 (lengthCopy [x,y+z,t] (x+y+z+t+2))=
      lengthCopy [0,x,y+z] 0 := by
  have h : x+y+z+t+2=x+(y+z)+t+2 := by omega
  rw [h,lengthCopy_three_last]
  simp only [lengthCopy,Nat.lt_irrefl,ite_false,ite_true,List.sum_cons,List.sum_nil,Nat.zero_add]
  unfold exchangeIndex
  rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
  omega

theorem lengthCopy_before (a : Nat) (ns : List Nat) (i : Nat) (hi : i<a) :
    lengthCopy (a::ns) i=i := by rw [lengthCopy,ite_eq_left hi]

theorem lengthCopy_here (a : Nat) (ns : List Nat) :
    lengthCopy (a::ns) a=a+ns.sum := by rw [lengthCopy,ite_eq_right (Nat.lt_irrefl _),ite_eq_left rfl]

theorem lengthCopy_after (a : Nat) (ns : List Nat) (i : Nat) (hi : a<i) :
    lengthCopy (a::ns) i=a+lengthCopy ns (i-a-1) := by
  rw [lengthCopy,ite_eq_right (by omega : ¬i<a),ite_eq_right (by omega : i≠a)]

theorem exchange_before_tail (s t i : Nat) (hi : i<s) : exchangeIndex s t 1 i=i := by
  rw [exchangeIndex,ite_eq_left hi]

theorem exchange_last_tail (s t : Nat) : exchangeIndex s t 1 (s+t)=s := by
  rw [exchangeIndex,ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
  omega

theorem exchange_inside_tail (s t k : Nat) (hk : k<t) :
    exchangeIndex s t 1 (s+k)=s+k+1 := by
  rw [exchangeIndex,ite_eq_right (by omega),ite_eq_left (by omega)]

theorem lengthCopy_drop_last (x b t i : Nat) (hi : i<x+b+t+2) :
    exchangeIndex (x+b) t 1 (lengthCopy [x,b,t] i)=lengthCopy [x,b] i := by
  by_cases h₀ : i<x
  · rw [lengthCopy_before _ _ _ h₀,lengthCopy_before _ _ _ h₀,exchange_before_tail _ _ _ (by omega)]
  · by_cases h₁ : i=x
    · subst i
      rw [lengthCopy_here,lengthCopy_here]
      simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
      rw [←Nat.add_assoc,exchange_last_tail]
    · have hx : x<i := by omega
      rw [lengthCopy_after _ _ _ hx,lengthCopy_after _ _ _ hx]
      by_cases h₂ : i-x-1<b
      · rw [lengthCopy_before _ _ _ h₂,lengthCopy_before _ _ _ h₂,exchange_before_tail _ _ _ (by omega)]
      · by_cases h₃ : i-x-1=b
        · rw [h₃,lengthCopy_here,lengthCopy_here]
          simp only [List.sum_cons,List.sum_nil,Nat.add_zero]
          rw [←Nat.add_assoc,exchange_last_tail]
        · have hb : b<i-x-1 := by omega
          rw [lengthCopy_after _ _ _ hb,lengthCopy_after _ _ _ hb]
          have hk : i-x-1-b-1<t := by omega
          rw [lengthCopy_before _ _ _ hk]
          change exchangeIndex (x+b) t 1 (x+(b+(i-x-1-b-1)))=x+(b+((i-x-1-b-1)+1))
          rw [←Nat.add_assoc,exchange_inside_tail _ _ _ hk]
          omega

theorem lengthCopy_rotate_tail (x y z t i : Nat) (hi : i<x+y+z+t+2) :
    exchangeIndex (x+y+z) t 1 (lengthCopy [x,y+z,t] i)=
      lengthCopy [0,x,y+z] (i+1) := by
  rw [lengthCopy_after _ _ _ (Nat.zero_lt_succ i)]
  simp only [Nat.zero_add,Nat.sub_zero]
  have he : i+1-1=i := by omega
  rw [he]
  have h:=lengthCopy_drop_last x (y+z) t i (by omega)
  simpa only [Nat.add_assoc] using h

end DosenPetric.Reduced.Gentzen
