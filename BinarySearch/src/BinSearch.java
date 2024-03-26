class BinSearch {
   private int a[];

  /*@ private normal_behavior
    @   requires   (\exists int idx; 0 <= idx < a.length; a[idx] == v);
    @   requires   (\forall int x, y; 0 <= x < y < a.length; a[x] <= a[y]);
    @   ensures    0 <= \result < a.length;
    @   ensures    a[\result] == v;
    @   assignable \nothing;
    @ also private exceptional_behavior
    @   requires   !(\exists int idx; 0 <= idx < a.length; a[idx] == v);
    @   assignable \nothing;
    @   signals_only RuntimeException;
    @*/
  private int binSearch(int v) {
    int low = 0;
    int up = a.length;
  
    /*@ loop_invariant 0 <= low <= up <= a.length;
      @ loop_invariant (\forall int x; 0 <= x < low; a[x] != v);
      @ loop_invariant (\forall int x; up <= x < a.length; a[x] != v);
      @ assignable \nothing;
      @ decreases up - low;
      @*/
    while (low < up) {
      int mid = low + ((up - low) / 2);
      if (v == a[mid]) { return mid;
      } else if (v < a[mid]) { up = mid;
      } else { low = mid + 1; }
    }
  
    throw new RuntimeException();
  }
}
