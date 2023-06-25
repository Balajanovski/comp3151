public class Test {
    public static void main(String[] args) throws InterruptedException {
        var array = new SortedArray(10);
        array.insert(5);
        array.insert(2);
        array.insert(3);
        array.insert(3);
        array.insert(2);
        array.print_sorted();

        System.out.println(array.member(3));
        System.out.println(array.member(4));
        System.out.println(array.member(6));
        System.out.println(array.member(1));

        System.out.println(array.member(3));
        array.delete(3);
        array.print_sorted();
        System.out.println(array.member(3));
        array.cleanup();
        array.print_sorted();
        System.out.println(array.member(3));
    }
}
