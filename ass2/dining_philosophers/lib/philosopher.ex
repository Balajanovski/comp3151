defmodule Philosopher do
  defstruct name: "",
            neighbor_pids: [],
            neighbor_forks: [],
            held_forks: [],
            clean_forks: [],
            promised_forks: []

  # Constructor

  def new_philosopher(name, neighbor_forks, held_forks) do
    receive do
      {:start, neighbor_pids} ->
        curr_pid = self()
        spawn_link(fn -> randomly_change_action(curr_pid) end)

        state = %Philosopher{
          name: name,
          neighbor_forks: neighbor_forks,
          held_forks: held_forks,
          neighbor_pids: neighbor_pids
        }

        thinking(state)
    end
  end

  # States

  defp thinking(state) do
    %{name: name} = state
    IO.puts("** #{name} is thinking.")

    receive do
      {:change_action} ->
        waiting_to_eat(state)

      {:fork_request, requester_pid, fork_id} ->
        if fork_neighbor?(fork_id, state) do
          if fork_clean?(fork_id, state) do
            thinking(promise_fork(requester_pid, fork_id, state))
          else
            thinking(give_fork(requester_pid, fork_id, state))
          end
        end
    end
  end

  defp waiting_to_eat(state) do
    %{name: name} = state
    IO.puts("#{name} wants to eat.")
    request_forks(state)
    wait_for_forks(state)
  end

  defp wait_for_forks(state) do
    if can_eat?(state) do
      eating(state)
    end

    receive do
      {:fork_request, requester_pid, fork_id} ->
        if fork_neighbor?(fork_id, state) do
          if fork_clean?(fork_id, state) do
            wait_for_forks(promise_fork(requester_pid, fork_id, state))
          else
            state = give_fork(requester_pid, fork_id, state)
            request_fork(requester_pid, fork_id)
            wait_for_forks(state)
          end
        end

      {:fork_response, fork_id} ->
        %{name: name, held_forks: held_forks, clean_forks: clean_forks} = state
        IO.puts("#{name} gets a fork.")

        wait_for_forks(%{
          state
          | held_forks: [fork_id | held_forks],
            clean_forks: [fork_id | clean_forks]
        })
    end
  end

  defp eating(state) do
    %{name: name} = state
    IO.puts("** #{name} is eating.")

    receive do
      {:change_action} ->
        state = give_promised_forks(state)
        state = make_all_forks_dirty(state)
        thinking(state)
    end
  end

  # Helpers

  defp request_forks(state) do
    %{neighbor_pids: neighbor_pids} = state
    missing = missing_forks(state)

    Enum.each(neighbor_pids, fn neighbor_pid ->
      Enum.each(missing, fn missing_fork ->
        request_fork(neighbor_pid, missing_fork)
      end)
    end)
  end

  defp request_fork(neighbor_pid, fork_id) do
    send(neighbor_pid, {:fork_request, self(), fork_id})
  end

  defp missing_forks(state) do
    %{neighbor_forks: neighbor_forks, held_forks: held_forks} = state
    neighbor_forks -- held_forks
  end

  defp make_all_forks_dirty(state) do
    %{state | clean_forks: []}
  end

  defp give_promised_forks(state) do
    %{
      name: name,
      promised_forks: promised_forks,
      held_forks: held_forks,
      clean_forks: clean_forks
    } = state

    given_fork_ids =
      Enum.map(promised_forks, fn {requester_pid, fork_id} ->
        IO.puts("#{name} gives a promised fork.")
        send(requester_pid, {:fork_response, fork_id})

        fork_id
      end)

    %{
      state
      | promised_forks: [],
        held_forks: held_forks -- given_fork_ids,
        clean_forks: clean_forks -- given_fork_ids
    }
  end

  defp promise_fork(requester_pid, fork_id, state) do
    %{name: name, promised_forks: promised_forks} = state
    IO.puts("#{name} promises a fork.")
    %{state | promised_forks: [{requester_pid, fork_id} | promised_forks]}
  end

  defp give_fork(requester_pid, fork_id, state) do
    %{name: name, held_forks: held_forks, clean_forks: clean_forks} = state
    IO.puts("#{name} gives a fork.")
    send(requester_pid, {:fork_response, fork_id})

    %{
      state
      | held_forks: List.delete(held_forks, fork_id),
        clean_forks: List.delete(clean_forks, fork_id)
    }
  end

  defp fork_clean?(fork_id, state) do
    %{clean_forks: clean_forks} = state
    fork_id in clean_forks
  end

  defp fork_neighbor?(fork_id, state) do
    %{neighbor_forks: neighbor_forks} = state
    fork_id in neighbor_forks
  end

  defp can_eat?(state) do
    length(missing_forks(state)) == 0
  end

  # Make it so that the philosophers' actions randomly change

  defp randomly_change_action(pid) do
    Process.sleep(Enum.random(1..5) * 1000)
    send(pid, {:change_action})
    randomly_change_action(pid)
  end
end
