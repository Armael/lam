### lam

#### alloc_stack

```
⟦alloc_stack (v ↦ eᵥ) (vₑ vₖ ↦ e_f)⟧ =
  λk k_f.
    k (λf x.
        f x
          (λv.     ⟦eᵥ⟧  (λv. v) k_f)
          (λvₑ vₖ. ⟦e_f⟧ (λv. v) k_f))
```

#### resume

```
⟦resume stack f v⟧ =
  λk k_f.
    ⟦v⟧ (λv.
      ⟦f⟧ (λf.
        ⟦stack⟧ (λstack.
          k (stack f v)
        ) k_f
      ) k_f
    ) k_f
```

#### perform

```
⟦perform e⟧ =
  λk k_f.
    ⟦e⟧ (λvₑ.
      k_f vₑ (λf v. f v k k_f)
    ) k_f
```

#### delegate

```
⟦delegate e stack⟧ =
  λk k_f.
    ⟦stack⟧ (λstack.
      ⟦e⟧ (λvₑ.
        k_f vₑ stack
      ) k_f
    ) k_f
```

#### sugar

```
let continue stack e =
  resume stack (λx. x) e

let discontinue stack exn =
  resume stack (λx. raise x) exn

let handle body (v ↦ eᵥ) (vₑ vₖ ↦ e_f) =
  resume (alloc_stack (v ↦ eᵥ) (vₑ vₖ ↦ e_f)) (λ(). body) ()
```
