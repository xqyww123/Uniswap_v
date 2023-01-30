

- envir: singleton {sender: address, code: address}
- contracts: address -> field-name -> Value

address := nat (it is logically abstract and inifinite therefore)
field-name := string
Value := usual-Value | mapping-id | array-id

mapping-id, array-id: MLP
  (id, type_k, type_v) -> Value -> Value
  (id, type_v) -> nat -> Value



