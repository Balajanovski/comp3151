defmodule DiningPhilosophers.CLI do
  def main(_) do
    IO.puts("Starting dining philosophers...")

    pid1 = spawn_link(fn -> Philosopher.new_philosopher("Nietzsche", [0, 4], [0, 4]) end)
    pid2 = spawn_link(fn -> Philosopher.new_philosopher("Kant", [0, 1], [1]) end)
    pid3 = spawn_link(fn -> Philosopher.new_philosopher("Descartes", [1, 2], [2]) end)
    pid4 = spawn_link(fn -> Philosopher.new_philosopher("Hegel", [2, 3], [3]) end)
    pid5 = spawn_link(fn -> Philosopher.new_philosopher("Kierkegaard", [3, 4], []) end)

    send(pid1, {:start, [pid2, pid5]})
    send(pid2, {:start, [pid1, pid3]})
    send(pid3, {:start, [pid2, pid4]})
    send(pid4, {:start, [pid3, pid5]})
    send(pid5, {:start, [pid4, pid1]})

    Process.sleep(20 * 1000)
  end
end
