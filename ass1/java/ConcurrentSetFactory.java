public class ConcurrentSetFactory implements ISetFactory {
    @Override
    public ISet construct(int N) {
        return new ConcurrentSet(N);
    }

    @Override
    public String get_name() {
        return "Concurrent Set";
    }
}
