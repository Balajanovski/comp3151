public class NaiveSetFactory implements ISetFactory {
    @Override
    public ISet construct(int N) {
        return new NaiveSet(N);
    }

    @Override
    public String get_name() {
        return "Naive Set";
    }
}
