public interface ISet {
    void insert(int x) throws InterruptedException;
    int[] get_values();
    void delete(int x);
    boolean member(int x);
    void print_sorted();
    void cleanup();
}
