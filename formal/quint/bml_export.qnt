// A deterministic one-state export; no sampling is used to select rows.
module bml_export {
  import traffic.* from "./traffic"
  var rows: List[List[int]]
  action init = rows' = transitionRows(1, 1)
    .concat(transitionRows(1, 2))
    .concat(transitionRows(2, 1))
    .concat(transitionRows(2, 2))
    .concat(transitionRows(3, 2))
    .concat(transitionRows(2, 3))
  action step = rows' = rows
}
