T = int(input())
for _ in range(T):
    N = int(input())
    goals = list(map(int, input().split()))
    dp = [0] * N
    min_goals = goals[0]
    for i in range(1, N):
        dp[i] = max(dp[i-1], goals[i] - min_goals)
        min_goals = min(min_goals, goals[i])
    if dp[-1] == 0:
        print("UNFIT")
    else:
        print(dp[-1])
