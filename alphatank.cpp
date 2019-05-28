#include <stack>
#include <list>
#include <set>
#include <string>
#include <iostream>
#include <ctime>
#include <cstring>
#include <queue>
#include <algorithm>
#include "jsoncpp/json.h"

using std::string;
using std::cin;
using std::cout;
using std::endl;
using std::flush;
using std::getline;
using std::queue;

clock_t startTime;
int cnt = 0;
string debug;

namespace TankGame {
    using std::min;
    using std::max;
    using std::list;
    using std::vector;
    using std::deque;
    using std::pair;
    using std::make_pair;
    using std::stack;
    using std::set;
    using std::istream;


    enum GameResult {
        NotFinished = -2,
        Draw = -1,
        Blue = 0,
        Red = 1
    };

    enum FieldItem {
        None = 0,
        Brick = 1,
        Steel = 2,
        Base = 4,
        Blue0 = 8,
        Blue1 = 16,
        Red0 = 32,
        Red1 = 64,
        Water = 128
    };

    template<class T>
    inline T sgn(T x) {
        if (x > 0)return 1;
        if (x < 0)return -1;
        return 0;
    }

    template<typename T>
    inline T operator~(T a) { return (T) ~(int) a; }

    template<typename T>
    inline T operator|(T a, T b) { return (T) ((int) a | (int) b); }

    template<typename T>
    inline T operator&(T a, T b) { return (T) ((int) a & (int) b); }

    template<typename T>
    inline T operator^(T a, T b) { return (T) ((int) a ^ (int) b); }

    template<typename T>
    inline T &operator|=(T &a, T b) { return (T &) ((int &) a |= (int) b); }

    template<typename T>
    inline T &operator&=(T &a, T b) { return (T &) ((int &) a &= (int) b); }

    template<typename T>
    inline T &operator^=(T &a, T b) { return (T &) ((int &) a ^= (int) b); }

    enum Action {
        Invalid = -2,
        Stay = -1,
        Up, Right, Down, Left,
        UpShoot, RightShoot, DownShoot, LeftShoot
    };

    char *ActionToString(Action act) {
        if (act == Invalid) return "Invalid";
        if (act == Stay) return "Stay";
        if (act == Up) return "Up";
        if (act == Right) return "Right";
        if (act == Down) return "Down";
        if (act == Left) return "Left";
        if (act == UpShoot) return "UpShoot";
        if (act == RightShoot) return "RightShoot";
        if (act == DownShoot) return "DownShoot";
        if (act == LeftShoot) return "LeftShoot";
    }

    // 坐标左上角为原点（0, 0），x 轴向右延伸，y 轴向下延伸
    // Side（对战双方） - 0 为蓝，1 为红
    // Tank（每方的坦克） - 0 为 0 号坦克，1 为 1 号坦克
    // Turn（回合编号） - 从 1 开始

    const int fieldHeight = 9, fieldWidth = 9, sideCount = 2, tankPerSide = 2;

    // 基地的横坐标
    const int baseX[sideCount] = {fieldWidth / 2, fieldWidth / 2};

    // 基地的纵坐标
    const int baseY[sideCount] = {0, fieldHeight - 1};

    const int dx[4] = {0, 1, 0, -1}, dy[4] = {-1, 0, 1, 0};
    const FieldItem tankItemTypes[sideCount][tankPerSide] = {
            {Blue0, Blue1},
            {Red0,  Red1}
    };

    int maxTurn = 100;

    inline Action Forward(int side) {
        return side == Blue ? Down : Up;
    }

    inline bool ActionIsMove(Action x) {
        return x >= Up && x <= Left;
    }

    inline bool ActionIsShoot(Action x) {
        return x >= UpShoot && x <= LeftShoot;
    }

    inline bool ActionDirectionIsOpposite(Action a, Action b) {
        return a >= Up && b >= Up && (a + 2) % 4 == b % 4;
    }

    inline bool CoordValid(int x, int y) {
        return x >= 0 && x < fieldWidth && y >= 0 && y < fieldHeight;
    }

    inline bool canStand(FieldItem item) {
        const int mask = Brick | Steel | Base | Water;
        return !(item & mask);
    }

    // 判断 item 是不是叠在一起的多个坦克
    inline bool HasMultipleTank(FieldItem item) {
        // 如果格子上只有一个物件，那么 item 的值是 2 的幂或 0
        // 对于数字 x，x & (x - 1) == 0 当且仅当 x 是 2 的幂或 0
        return !!(item & (item - 1));
    }

    inline int GetTankSide(FieldItem item) {
        return item == Blue0 || item == Blue1 ? Blue : Red;
    }

    inline int GetTankID(FieldItem item) {
        return item == Blue0 || item == Red0 ? 0 : 1;
    }

    // 获得动作的方向
    inline int ExtractDirectionFromAction(Action x) {
        if (x >= Up)
            return x % 4;
        return -1;
    }

    // 物件消失的记录，用于回退
    struct DisappearLog {
        FieldItem item;

        // 导致其消失的回合的编号
        int turn;

        int x, y;

        bool operator<(const DisappearLog &b) const {
            if (x == b.x) {
                if (y == b.y)
                    return item < b.item;
                return y < b.y;
            }
            return x < b.x;
        }
    };

    namespace Utility {

        pair<int, int> q[fieldHeight * fieldWidth];
        int head, tail;

        void BFSDistance(int x, int y, FieldItem (*gameField)[fieldWidth], int (*dis)[fieldWidth]) {
            for (int i = 0; i < fieldHeight; ++i)for (int j = 0; j < fieldWidth; ++j)dis[i][j] = (int) 1e9;
            dis[y][x] = 0;
            head = 0;
            tail = 0;
            q[tail++] = make_pair(x, y);
            while (head < tail) {
                auto[tx, ty]=q[head];
                int d = dis[ty][tx];
                for (int i = head; i < tail; ++i) {
                    auto p = q[i];
                    if (dis[p.second][p.first] > d)break;
                    for (int o = 0; o < 4; ++o) {
                        int nx = p.first + dx[o];
                        int ny = p.second + dy[o];
                        if (CoordValid(nx, ny) && (gameField[ny][nx] & (Brick | Steel | Water)) == 0 &&
                            dis[ny][nx] == (int) 1e9) {
                            dis[ny][nx] = d + 1;
                            if (gameField[ny][nx] != Base)q[tail++] = make_pair(nx, ny);
                        }
                    }
                }
                while (head < tail) {
                    auto[ttx, tty]=q[head];
                    if (dis[tty][ttx] > d)break;
                    ++head;
                    for (int o = 0; o < 4; ++o) {
                        int nx = ttx + dx[o];
                        int ny = tty + dy[o];
                        if (CoordValid(nx, ny) && (gameField[ny][nx] & (Steel | Base | Water)) == 0 &&
                            (gameField[ny][nx] & Brick) != 0 &&
                            dis[ny][nx] == (int) 1e9) {
                            dis[ny][nx] = d + 2;
                            q[tail++] = make_pair(nx, ny);
                        }
                    }
                }
            }
        }


        void BFSBestPath(int baseY, FieldItem (*gameField)[fieldWidth], int (*dis)[fieldWidth],
                         bool (*goodPath)[fieldWidth], bool (*goodDir)[fieldHeight][4]) {
            memset(goodDir, 0, sizeof(&goodDir));
            head = 0;
            tail = 0;
            for (int tx = 0; tx < fieldWidth; ++tx)
                for (int ty = 0; ty < fieldHeight; ++ty)
                    if (goodPath[ty][tx])q[tail++] = make_pair(tx, ty);
            while (head < tail) {
                auto[x, y]=q[head++];
                for (int o = 0; o < 4; ++o) {
                    int nx = x - dx[o];
                    int ny = y - dy[o];
                    if (CoordValid(nx, ny) && !goodPath[ny][nx] &&
                        dis[y][x] - dis[ny][nx] == ((gameField[y][x] & Brick) ? 2 : 1)) {
                        goodPath[ny][nx] = true;
                        goodDir[ny][nx][o] = true;
                        q[tail++] = make_pair(nx, ny);
                    }
                }
            }
        }

        bool vis[fieldHeight][fieldWidth];

        // water don't block the way
        void dfs(int x1, int y1, FieldItem (*gameField)[fieldWidth]) {
            vis[y1][x1] = true;
            for (int i = 0; i < 4; ++i) {
                int x = x1 + dx[i], y = y1 + dy[i];
                if (CoordValid(x, y) && !vis[y][x] && (gameField[y][x] & (Brick | Steel | Base | Water)) == 0) {
                    dfs(x, y, gameField);
                }
            }
        }

        bool IsLink(int x1, int y1, int x2, int y2, FieldItem (*gameField)[fieldWidth]) {
            if (x1 == -1 || x2 == -1)return false;
            memset(vis, 0, sizeof(vis));
            if (gameField[y1][x1] & (Brick | Steel | Base | Water))return 0;
            dfs(x1, y1, gameField);
            return vis[y2][x2];
        }
    }

    class TankField {
    public:
        //!//!//!// 以下变量设计为只读，不推荐进行修改 //!//!//!//

        // 游戏场地上的物件（一个格子上可能有多个坦克）
        FieldItem gameField[fieldHeight][fieldWidth] = {};

        // 坦克是否存活
        bool tankAlive[sideCount][tankPerSide] = {{true, true},
                                                  {true, true}};

        // 基地是否存活
        bool baseAlive[sideCount] = {true, true};

        // 坦克横坐标，-1表示坦克已炸
        int tankX[sideCount][tankPerSide] = {
                {fieldWidth / 2 - 2, fieldWidth / 2 + 2},
                {fieldWidth / 2 + 2, fieldWidth / 2 - 2}
        };

        // 坦克纵坐标，-1表示坦克已炸
        int tankY[sideCount][tankPerSide] = {{0,               0},
                                             {fieldHeight - 1, fieldHeight - 1}};

        // 当前回合编号
        int currentTurn = 1;

        // 我是哪一方
        int mySide;

        // 用于回退的log
        stack<DisappearLog> logs;

        // 过往动作（previousActions[x] 表示所有人在第 x 回合的动作，第 0 回合的动作没有意义）
        Action previousActions[106][sideCount][tankPerSide] = {{{Stay, Stay}, {Stay, Stay}}};

        //!//!//!// 以上变量设计为只读，不推荐进行修改 //!//!//!//

        // 本回合双方即将执行的动作，需要手动填入
        Action nextAction[sideCount][tankPerSide] = {{Invalid, Invalid},
                                                     {Invalid, Invalid}};

        // 判断行为是否合法（出界或移动到非空格子算作非法）
        // 未考虑坦克是否存活
        bool ActionIsValid(int side, int tank, Action act) {
            if (!tankAlive[side][tank] && act != Stay)return false;
            if (act == Invalid)
                return false;
            if (act > Left && previousActions[currentTurn - 1][side][tank] > Left) // 连续两回合射击
                return false;
            if (act == Stay || act > Left)
                return true;
            int x = tankX[side][tank] + dx[act],
                    y = tankY[side][tank] + dy[act];
            return CoordValid(x, y) && gameField[y][x] == None;
        }

        bool CanMove(int x, int y, Action act) {
            x += dx[act];
            y += dy[act];
            return CoordValid(x, y) && gameField[y][x] == None;
        }

        // 判断 nextAction 中的所有行为是否都合法
        // 忽略掉未存活的坦克
        bool ActionIsValid() {
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    if (tankAlive[side][tank] && !ActionIsValid(side, tank, nextAction[side][tank]))
                        return false;
            return true;
        }

    private:
        void _destroyTank(int side, int tank) {
            tankAlive[side][tank] = false;
            tankX[side][tank] = tankY[side][tank] = -1;
        }

        void _revertTank(int side, int tank, DisappearLog &log) {
            int &currX = tankX[side][tank], &currY = tankY[side][tank];
            if (tankAlive[side][tank])
                gameField[currY][currX] &= ~tankItemTypes[side][tank];
            else
                tankAlive[side][tank] = true;
            currX = log.x;
            currY = log.y;
            gameField[currY][currX] |= tankItemTypes[side][tank];
        }

    public:

        bool hasDestroyBlock[sideCount][tankPerSide][106];

        // 执行 nextAction 中指定的行为并进入下一回合，返回行为是否合法
        bool DoAction() {
            if (!ActionIsValid())
                return false;

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    hasDestroyBlock[side][tank][currentTurn] = false;
            // 1 移动
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++) {
                    Action act = nextAction[side][tank];

                    // 保存动作
                    previousActions[currentTurn][side][tank] = act;
                    if (tankAlive[side][tank] && ActionIsMove(act)) {
                        int &x = tankX[side][tank], &y = tankY[side][tank];
                        FieldItem &items = gameField[y][x];

                        // 记录 Log
                        DisappearLog log;
                        log.x = x;
                        log.y = y;
                        log.item = tankItemTypes[side][tank];
                        log.turn = currentTurn;
                        logs.push(log);

                        // 变更坐标
                        x += dx[act];
                        y += dy[act];

                        // 更换标记（注意格子可能有多个坦克）
                        gameField[y][x] |= log.item;
                        items &= ~log.item;
                    }
                }

            // 2 射♂击
            set<DisappearLog> itemsToBeDestroyed;
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++) {
                    Action act = nextAction[side][tank];
                    if (tankAlive[side][tank] && ActionIsShoot(act)) {
                        int dir = ExtractDirectionFromAction(act);
                        int x = tankX[side][tank], y = tankY[side][tank];
                        bool hasMultipleTankWithMe = HasMultipleTank(gameField[y][x]);
                        while (true) {
                            x += dx[dir];
                            y += dy[dir];
                            if (!CoordValid(x, y))break;
                            FieldItem items = gameField[y][x];
                            if (items != None && items != Water) {
                                // 对射判断
                                if (items >= Blue0 &&
                                    !hasMultipleTankWithMe && !HasMultipleTank(items)) {
                                    // 自己这里和射到的目标格子都只有一个坦克
                                    Action theirAction = nextAction[GetTankSide(items)][GetTankID(items)];
                                    if (ActionIsShoot(theirAction) &&
                                        ActionDirectionIsOpposite(act, theirAction)) {
                                        // 而且我方和对方的射击方向是反的
                                        // 那么就忽视这次射击
                                        break;
                                    }
                                }

                                // 标记这些物件要被摧毁了（防止重复摧毁）
                                for (int mask = 1; mask <= Red1; mask <<= 1)
                                    if (items & mask) {
                                        hasDestroyBlock[side][tank][currentTurn] = true;
                                        DisappearLog log;
                                        log.x = x;
                                        log.y = y;
                                        log.item = (FieldItem) mask;
                                        log.turn = currentTurn;
                                        itemsToBeDestroyed.insert(log);
                                    }
                                break;
                            }
                        }
                    }
                }

            for (auto &log : itemsToBeDestroyed) {
                switch (log.item) {
                    case Base: {
                        int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                        baseAlive[side] = false;
                        break;
                    }
                    case Blue0:
                        _destroyTank(Blue, 0);
                        break;
                    case Blue1:
                        _destroyTank(Blue, 1);
                        break;
                    case Red0:
                        _destroyTank(Red, 0);
                        break;
                    case Red1:
                        _destroyTank(Red, 1);
                        break;
                    case Steel:
                        continue;
                    default:;
                }
                gameField[log.y][log.x] &= ~log.item;
                logs.push(log);
            }

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    nextAction[side][tank] = Invalid;

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    hasInit[side][tank] = false;

            currentTurn++;
            return true;
        }

        // 回到上一回合
        bool Revert() {
            if (currentTurn == 1)
                return false;

            currentTurn--;
            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++)
                    hasInit[side][tank] = false;
            while (!logs.empty()) {
                DisappearLog &log = logs.top();
                if (log.turn == currentTurn) {
                    logs.pop();
                    switch (log.item) {
                        case Base: {
                            int side = log.x == baseX[Blue] && log.y == baseY[Blue] ? Blue : Red;
                            baseAlive[side] = true;
                            gameField[log.y][log.x] = Base;
                            break;
                        }
                        case Brick:
                            gameField[log.y][log.x] = Brick;
                            break;
                        case Blue0:
                            _revertTank(Blue, 0, log);
                            break;
                        case Blue1:
                            _revertTank(Blue, 1, log);
                            break;
                        case Red0:
                            _revertTank(Red, 0, log);
                            break;
                        case Red1:
                            _revertTank(Red, 1, log);
                            break;
                        default:;
                    }
                } else
                    break;
            }
            return true;
        }

        // 游戏是否结束？谁赢了？
        GameResult GetGameResult() {
            bool fail[sideCount] = {};
            for (int side = 0; side < sideCount; side++)
                if ((!tankAlive[side][0] && !tankAlive[side][1]) || !baseAlive[side])
                    fail[side] = true;
            if (fail[0] == fail[1])
                return fail[0] || currentTurn > 105 ? Draw : NotFinished; // TODO: why 105 ???
            if (fail[Blue])
                return Red;
            return Blue;
        }

        GameResult GetGameResult(int side, int tank) {
            if (!baseAlive[side] && !baseAlive[!side])return Draw;
            if (!baseAlive[0])return Red;
            if (!baseAlive[1])return Blue;
            if (!tankAlive[side][tank])return (GameResult) !side;
            return currentTurn > 105 ? Draw : NotFinished;
        }

        // 三个 int 表示场地 01 矩阵（每个 int 用 27 位表示 3 行）
        // why only hasBrick
        TankField(int hasBrick[3], int hasWater[3], int hasSteel[3], int mySide) : mySide(mySide) {
//        TankField(int hasBrick[3], int mySide) : mySide(mySide) {
            for (int i = 0; i < 3; i++) {
                int mask = 1;
                for (int y = i * 3; y < (i + 1) * 3; y++) {
                    for (int x = 0; x < fieldWidth; x++) {
                        if (hasBrick[i] & mask)
                            gameField[y][x] = Brick;
                        else if (hasWater[i] & mask)
                            gameField[y][x] = Water;
                        else if (hasSteel[i] & mask)
                            gameField[y][x] = Steel;
                        mask <<= 1;
                    }
                }
            }
            for (int side = 0; side < sideCount; side++) {
                for (int tank = 0; tank < tankPerSide; tank++)
                    gameField[tankY[side][tank]][tankX[side][tank]] = tankItemTypes[side][tank];
                gameField[baseY[side]][baseX[side]] = Base;
            }
        }

        // 打印场地
        void DebugPrint() {
#ifndef _BOTZONE_ONLINE
            const string side2String[] = {"蓝", "红"};
            const string boolean2String[] = {"已炸", "存活"};
            const char *boldHR = "==============================";
            const char *slimHR = "------------------------------";
            cout << boldHR << endl
                 << "图例：" << endl
                 << ". - 空\t# - 砖\t% - 钢\t* - 基地\t@ - 多个坦克" << endl
                 << "b - 蓝0\tB - 蓝1\tr - 红0\tR - 红1\tW - 水" << endl //Tank2 feature
                 << slimHR << endl;
            for (int y = 0; y < fieldHeight; y++) {
                for (int x = 0; x < fieldWidth; x++) {
                    switch (gameField[y][x]) {
                        case None:
                            cout << '.';
                            break;
                        case Brick:
                            cout << '#';
                            break;
                        case Steel:
                            cout << '%';
                            break;
                        case Base:
                            cout << '*';
                            break;
                        case Blue0:
                            cout << 'b';
                            break;
                        case Blue1:
                            cout << 'B';
                            break;
                        case Red0:
                            cout << 'r';
                            break;
                        case Red1:
                            cout << 'R';
                            break;
                        case Water:
                            cout << 'W';
                            break;
                        default:
                            cout << '@';
                            break;
                    }
                }
                cout << endl;
            }
            cout << slimHR << endl;
            for (int side = 0; side < sideCount; side++) {
                cout << side2String[side] << "：基地" << boolean2String[baseAlive[side]];
                for (int tank = 0; tank < tankPerSide; tank++)
                    cout << ", 坦克" << tank << boolean2String[tankAlive[side][tank]];
                cout << endl;
            }
            cout << "当前回合：" << currentTurn << "，";
            GameResult result = GetGameResult();
            if (result == -2)
                cout << "游戏尚未结束" << endl;
            else if (result == -1)
                cout << "游戏平局" << endl;
            else
                cout << side2String[result] << "方胜利" << endl;
            cout << boldHR << endl;
#endif
        }

        bool operator!=(const TankField &b) const {

            for (int y = 0; y < fieldHeight; y++)
                for (int x = 0; x < fieldWidth; x++)
                    if (gameField[y][x] != b.gameField[y][x])
                        return true;

            for (int side = 0; side < sideCount; side++)
                for (int tank = 0; tank < tankPerSide; tank++) {
                    if (tankX[side][tank] != b.tankX[side][tank])
                        return true;
                    if (tankY[side][tank] != b.tankY[side][tank])
                        return true;
                    if (tankAlive[side][tank] != b.tankAlive[side][tank])
                        return true;
                }

            if (baseAlive[0] != b.baseAlive[0] ||
                baseAlive[1] != b.baseAlive[1])
                return true;

            if (currentTurn != b.currentTurn)
                return true;

            return false;
        }

        bool JustShoot(int side, int tank) {
            return previousActions[currentTurn - 1][side][tank] > Left;
        }

        bool CanShootEachOther(int x1, int y1, int x2, int y2) {
            if (x1 == x2) {
                if (y1 > y2)std::swap(y1, y2);
                for (int i = y1 + 1; i < y2; ++i)if (gameField[i][x1] & 7)return false;
                return true;
            } else if (y1 == y2) {
                if (x1 > x2)std::swap(x1, x2);
                for (int i = x1 + 1; i < x2; ++i)if (gameField[y1][i] & 7)return false;
                return true;
            }
            return false;
        }

        bool CanTankShootEachOther(int side1, int tank1, int side2, int tank2) {
            if (!tankAlive[side1][tank1] || !tankAlive[side2][tank2])return false;
            return CanShootEachOther(tankX[side1][tank1], tankY[side1][tank1],
                                     tankX[side2][tank2], tankY[side2][tank2]);
        }

        bool CanTankShootEachOther(int side, int tank) {
            if (!tankAlive[side][tank] || !tankAlive[!side][!tank])return false;
            return CanShootEachOther(tankX[side][tank], tankY[side][tank], tankX[!side][!tank], tankY[!side][!tank]);
        }

        bool CrossShoot(int side, int tank) {
            if (CanShootEachOther(tankX[side][tank], tankY[side][tank], baseX[!side], baseY[!side]) &&
                !JustShoot(side, tank))
                return false;
            if (CanTankShootEachOther(side, tank, !side, tank) && CanTankShootEachOther(side, tank, !side, !tank) &&
                !JustShoot(!side, tank) && !JustShoot(!side, !tank)) {
                return !(tankX[!side][tank] == tankX[!side][!tank] || tankY[!side][tank] == tankY[!side][!tank]);
            }
            return false;
        }

        bool WillKill(int side1, int tank1, Action act1, int side2, int tank2, Action act2) {
            for (int i = 0; i < 2; ++i)for (int j = 0; j < 2; ++j)nextAction[i][j] = Stay;
            nextAction[side1][tank1] = act1;
            nextAction[side2][tank2] = act2;
            DoAction();
            bool flag = !tankAlive[side2][tank2];
            Revert();
            return flag;
        }

        bool MayShooting(int side, int tank, Action act, int tarX, int tarY) {
            if (!ActionIsShoot(act))return false;
            int d = act - 4;
            int x = tankX[side][tank] + dx[d], y = tankY[side][tank] + dy[d];
            while (CoordValid(x, y)) {
                if (x == tarX && y == tarY)return true;
                if (gameField[y][x] & 7)break;
                x += dx[d];
                y += dy[d];
            }
            return false;
        }

        bool MayKill(int side1, int tank1, Action act1, int side2, int tank2, Action act2) {
            if (ActionIsShoot(act1) && ActionIsShoot(act2) && ActionDirectionIsOpposite(act1, act2))return false;
            int x = tankX[side2][tank2], y = tankY[side2][tank2];
            if (ActionIsMove(act2)) {
                x += dx[act2];
                y += dy[act2];
            }
            return MayShooting(side1, tank1, act1, x, y);
        }

        bool MayStack(int side1, int tank1, Action act1, int side2, int tank2, Action act2) {
            if (!ActionIsMove(act1) || !ActionIsMove(act2))return false;
            int x1 = tankX[side1][tank1] + dx[act1], y1 = tankY[side1][tank1] + dy[act1];
            int x2 = tankX[side2][tank2] + dx[act2], y2 = tankY[side2][tank2] + dy[act2];
            return x1 == x2 && y1 == y2;
        }

        bool IsLink(int x1, int y1, int x2, int y2) {
            return Utility::IsLink(x1, y1, x2, y2, gameField);
        }

        bool IsTankLink(int side1, int tank1, int side2, int tank2) {
            return IsLink(tankX[side1][tank1], tankY[side1][tank1], tankX[side2][tank2], tankY[side2][tank2]);
        }

        bool OneSide() {
            return !IsTankLink(mySide, 0, mySide, 1) && !IsTankLink(mySide, 0, !mySide, 0) &&
                   !IsTankLink(mySide, 1, !mySide, 1);
        }

        int dis[sideCount][tankPerSide][fieldHeight][fieldWidth]{0};
        int attackDis[sideCount][tankPerSide]{0};
        bool goodPath[sideCount][tankPerSide][fieldHeight][fieldWidth]{false};
        bool goodDir[sideCount][tankPerSide][fieldHeight][fieldWidth][4]{false};
        bool hasInit[sideCount][tankPerSide];

//  TODO: need revisement due to water
        void InitDistance(int side, int tank) {
            if (hasInit[side][tank])return;
            hasInit[side][tank] = true;
            int tmp = tankY[!side][!tank] + dy[Forward(!side)];
//            if (tankAlive[!side][!tank]) {
//                if (IsTankLink(side, tank, !side, !tank) && !WillCounter(side, tank)) {
//                    while (CoordValid(tankX[!side][!tank], tmp) &&
//                           gameField[tmp][tankX[!side][!tank]] == None)
//                        tmp += dy[Forward(!side)];
//                }
//                for (int i = tankY[!side][!tank] + dy[Forward(!side)]; i != tmp; i += dy[Forward(!side)])
//                    gameField[i][tankX[!side][!tank]] = Steel;
//            }
            Utility::BFSDistance(tankX[side][tank], tankY[side][tank], gameField, dis[side][tank]);
//            if (tankAlive[!side][!tank]) {
//                for (int i = tankY[!side][!tank] + dy[Forward(!side)]; i != tmp; i += dy[Forward(!side)])
//                    gameField[i][tankX[!side][!tank]] = None;
//            }
            int ret = (int) 1e9;
            if ((side ^ tank) == 0) {
                for (int tx = baseX[!side] - 1, det = 0; tx >= 0; --tx) {
                    if (dis[side][tank][baseY[!side]][tx] + det < ret)ret = dis[side][tank][baseY[!side]][tx] + det;
                    if (gameField[baseY[!side]][tx] & Brick)det += 2;
                    if (gameField[baseY[!side]][tx] & Steel)det = (int) 1e9;
                }
            } else {
                for (int tx = baseX[!side] + 1, det = 0; tx < fieldWidth; ++tx) {
                    if (dis[side][tank][baseY[!side]][tx] + det < ret)ret = dis[side][tank][baseY[!side]][tx] + det;
                    if (gameField[baseY[!side]][tx] & Brick)det += 2;
                    if (gameField[baseY[!side]][tx] & Steel)det = (int) 1e9;
                }
            }
            int dty = dy[Forward(side)];
            for (int ty = baseY[!side] - dty, det = 0; (gameField[baseX[!side]][ty] & Steel) == 0; ty -= dty) {
                if (dis[side][tank][ty][baseX[!side]] + det < ret)ret = dis[side][tank][ty][baseX[!side]] + det;
                if (gameField[ty][baseX[!side]] & Brick)det += 2;
                if (gameField[ty][baseX[!side]] & Steel)det = (int) 1e9;
            }
            attackDis[side][tank] = ret + 1 + (tankY[side][tank] == baseY[!side] && JustShoot(side, tank));
            for (int i = 0; i < fieldHeight; ++i)for (int j = 0; j < fieldWidth; ++j)goodPath[side][tank][i][j] = false;
            if ((side ^ tank) == 0) {
                for (int tx = baseX[!side] - 1, det = 0; tx >= 0; --tx) {
                    if (dis[side][tank][baseY[!side]][tx] + det == ret)goodPath[side][tank][baseY[!side]][tx] = true;
                    if (gameField[baseY[!side]][tx] & Brick)det += 2;
                    if (gameField[baseY[!side]][tx] & Steel)det = (int) 1e9;
                }
            } else {
                for (int tx = baseX[!side] + 1, det = 0; tx < fieldWidth; ++tx) {
                    if (dis[side][tank][baseY[!side]][tx] + det == ret)goodPath[side][tank][baseY[!side]][tx] = true;
                    if (gameField[baseY[!side]][tx] & Brick)det += 2;
                    if (gameField[baseY[!side]][tx] & Steel)det = (int) 1e9;
                }
            }
            for (int ty = baseY[!side] - dty, det = 0; (gameField[baseX[!side]][ty] & Steel) == 0; ty -= dty) {
                if (dis[side][tank][ty][baseX[!side]] + det == ret)goodPath[side][tank][ty][baseX[!side]] = true;
                if (gameField[ty][baseX[!side]] & Brick)det += 2;
                if (gameField[ty][baseX[!side]] & Steel)det = (int) 1e9;
            }
            Utility::BFSBestPath(baseY[!side], gameField, dis[side][tank], goodPath[side][tank], goodDir[side][tank]);
        }

        void AnotherDistance(int side, int tank) {
            int ret = (int) 1e9;
            if (side ^ tank) {
                for (int tx = baseX[!side] - 1, det = 0; tx >= 0; --tx) {
                    if (dis[side][tank][baseY[!side]][tx] + det < ret)ret = dis[side][tank][baseY[!side]][tx] + det;
                    if (gameField[baseY[!side]][tx] & Brick)det += 2;
                    if (gameField[baseY[!side]][tx] & Steel)det = (int) 1e9;
                }
            } else {
                for (int tx = baseX[!side] + 1, det = 0; tx < fieldWidth; ++tx) {
                    if (dis[side][tank][baseY[!side]][tx] + det < ret)ret = dis[side][tank][baseY[!side]][tx] + det;
                    if (gameField[baseY[!side]][tx] & Brick)det += 2;
                    if (gameField[baseY[!side]][tx] & Steel)det = (int) 1e9;
                }
            }
            attackDis[side][tank] = min(attackDis[side][tank], ret + 1);
        }

        bool Defensible(int side, int tank) {
            if (!baseAlive[side])return false;
            if (!tankAlive[side][tank])return false;
            if (!tankAlive[!side][!tank])return true;
            InitDistance(side, tank);
            InitDistance(!side, !tank);
            if ((side ^ tank) == 0) {
                for (int x = baseX[side] - 1, det = 0, mn = (int) 1e9; x >= 0; --x) {
                    if (mn > dis[!side][!tank][baseY[side]][x] + det &&
                        dis[side][tank][baseY[side]][x] >= dis[!side][!tank][baseY[side]][x])
                        return false;
                    mn = min(mn, dis[side][tank][baseY[side]][x]);
                    if (gameField[baseY[!side]][x] & Brick)det += 2;
                }
            } else {
                for (int x = baseX[side] + 1, det = 0, mn = (int) 1e9; x <= fieldWidth; ++x) {
                    if (mn > dis[!side][!tank][baseY[side]][x] + det &&
                        dis[side][tank][baseY[side]][x] >= dis[!side][!tank][baseY[side]][x])
                        return false;
                    mn = min(mn, dis[side][tank][baseY[side]][x]);
                    if (gameField[baseY[!side]][x] & Brick)det += 2;
                }
            }
            if (tankY[side][tank] == baseY[side] && std::abs(tankX[side][tank] - baseX[side]) == 1) {
                if (CanTankShootEachOther(side, tank) && JustShoot(side, tank) && !JustShoot(!side, !tank))return false;
            }
            return true;
        }

        int getDirection(int x1, int y1, int x2, int y2) {
            if (x1 == x2) return y1 < y2 ? 2 : 0;
            if (y1 == y2) return x1 < x2 ? 1 : 3;
            return -1;
        }

        int getDirection(int side, int tank) {
            return getDirection(tankX[side][tank], tankY[side][tank], tankX[!side][!tank], tankY[!side][!tank]);
        }

        int GetCorner(int side, int tank) {
            int d = getDirection(!side, !tank);
            int x = tankX[side][tank], y = tankY[side][tank];
            int ret = 0;
            while (CoordValid(x, y)) {
                for (int o = 0; o < 4; ++o) {
                    if (goodDir[side][tank][y][x][o]) {
                        int nx = x + dx[o], ny = y + dy[o];
                        if (CoordValid(nx, ny) && o != d) return ret;
                    }
                }
                ++ret;
                x += dx[d];
                y += dy[d];
            }
            return -1;
        }

        bool canDefense(int side, int tank) {
            return abs(tankX[!side][!tank] - baseX[side]) + abs(tankY[!side][!tank] - baseY[side]) >
                   abs(tankX[side][tank] - baseX[side]) + abs(tankY[side][tank] - baseY[side]);
        }

        bool IsCounter(int x_1, int y_1, int x_2, int y_2) {
            if (x_1 != x_2)return false;
            if (y_1 == y_2)return false;
            if (!CanShootEachOther(x_1, y_1, x_2, y_2))return false;
            int y = (y_1 + y_2);
            int x = x_1;
            int y1, y2;
            if (y & 1)y1 = y / 2, y2 = y / 2 + 1;
            else y1 = y / 2, y2 = y / 2;
            if ((CanMove(x, y1, Left) || CanMove(x, y1, Right)) &&
                (CanMove(x, y2, Left) || CanMove(x, y2, Right)))
                return false;
            return true;
        }

        bool IsCounter(int side, int tank) {
            if (JustShoot(side, tank) != JustShoot(!side, !tank))return false;
            return IsCounter(tankX[side][tank], tankY[side][tank], tankX[!side][!tank], tankY[!side][!tank]);
        }

        bool WillCounter(int side, int tank) {
            if (!canDefense(side, tank))return false;
            if (IsCounter(side, tank))return true;
            if (tankX[side][tank] == tankX[!side][!tank])return false;
            if (std::abs(tankX[side][tank] - tankX[!side][!tank]) > 1)return false;
            if (CanShootEachOther(tankX[side][tank], tankY[side][tank], tankX[side][tank], tankY[!side][!tank]) &&
                !JustShoot(side, tank)) {
                return IsCounter(tankX[side][tank], tankY[side][tank] + dy[Forward(side)],
                                 tankX[side][tank], tankY[!side][!tank]);
            }
            if (CanShootEachOther(tankX[!side][!tank], tankY[side][tank], tankX[!side][!tank], tankY[!side][!tank]) &&
                !JustShoot(!side, !tank)) {
                return IsCounter(tankX[!side][!tank], tankY[!side][!tank] + dy[Forward(!side)],
                                 tankX[side][!tank], tankY[side][tank]);
            }
            return false;
        }

        bool inHome(int side, int tank) {
            if (side == Blue)return tankY[side][tank] <= 3;
            else return tankY[side][tank] >= 5;
        }

        bool inEnemy(int side, int tank) {
            if (side == Red)return tankY[side][tank] <= 3;
            else return tankY[side][tank] >= 5;
        }

        bool BlocksBetween(int side, int tank) {
            int x = tankX[side][tank], y = tankY[side][tank];
            if ((side ^ tank) == 0) {
                ++x;
                while (CoordValid(x, y) && x < tankX[side][!tank]) {
                    if (gameField[y][x] == Brick && gameField[4][x] == Brick)return true;
                    ++x;
                }
            } else {
                --x;
                while (CoordValid(x, y) && x > tankX[side][!tank]) {
                    if (gameField[y][x] == Brick && gameField[4][x] == Brick)return true;
                    --x;
                }
            }
            return false;
        }

        bool IsDefensing(int side, int tank) {
            int x, y;
            if (side == Blue)y = 0; else y = fieldHeight - 1;
            if (side ^ tank)x = 5; else x = 3;
            return tankX[side][tank] == x && tankY[side][tank] == y;
        }

        int EstimateAttack(int side, int tank) {
            if (!tankAlive[side][tank])return (int) -1e8;
            InitDistance(side, tank);
            if (!tankAlive[!side][!tank])return (int) 1e8 - attackDis[side][tank];
            InitDistance(!side, !tank);
            if (!canDefense(side, tank)) {
                return 500 * (attackDis[!side][!tank] - attackDis[side][tank]);
            }
//            if (attackDis[side][tank] <= attackDis[!side][!tank])return 10 * (20 - attackDis[side][tank]);
//            if (goodPath[!side][!tank][tankY[side][tank]][tankX[side][tank]])return -dis[!side][!tank][tankY[side][tank]][tankX[side][tank]];
//            else return -100;
            return 50 * (attackDis[!side][!tank] - attackDis[side][tank]) + 6 * (10 - attackDis[side][tank]);
//            ret += BlocksBetween(!side, !tank) - BlocksBetween(side, tank);
//            if (IsLink(tankX[side][tank], tankY[side][tank], tankX[!side][!tank], tankY[!side][!tank])) {
//                if (VerticalDis(side, tank) <= 0 ||
//                    dis[side][tank][baseY[side]][baseX[side]] >= dis[!side][!tank][baseY[side]][baseX[side]]) {
//                    if (CanTankShootEachOther(side, tank)) {
//                        int c1 = GetCorner(!side, !tank), c2 = GetCorner(side, tank);
//                        if (c1 == -1 && c2 == -1);
//                        else if (c1 == -1)ret -= 5 * (c2 + 1);
//                        else if (c2 == -1)ret += 5 * (c1 + 1);
//                        else ret += 5 * sgn(c1 - c2);
//                    }
//                    return 10000 * ret - 500;
//                }
//                if (WillCounter(side, tank)) {
//                    ret = 0;
//                }
//                return 100 * ret;
//            } else {
//                if (gameField[4][tankX[!side][!tank]] != Brick &&
//                    gameField[4 + dy[Forward(!side)]][tankX[!side][!tank]] == Brick)
//                    ret -= 50;
//            }
//            return ret;
        }

        int EstimateAttack(int side) {
            return EstimateAttack(side, 0) + EstimateAttack(side, 1);
        }

        bool inLine(int side, int tank) {
            if (gameField[4][tankX[side][tank]] != Brick)return false;
            if (side == Blue)return tankY[side][tank] == 3;
            return tankY[side][tank] == 5;
        }

        pair<int, int> TempMove(Action act0) {
            if (ActionIsMove(act0))return make_pair(dx[act0], dy[act0]);
            return make_pair(0, 0);
        }

        template<typename... Actions>
        pair<int, int> TempMove(Action act0, Actions... acts) {
            auto ret = TempMove(acts...);
            if (ActionIsMove(act0))ret.first += dx[act0], ret.second += dy[act0];
            return ret;
        }

        template<typename... Actions>
        bool NoMove(Actions... acts) {
            return TempMove(acts...) == make_pair(0, 0);
        }

        Action GetPattern(int side, int tank) {
            for (int cycle = 1; cycle <= 8; ++cycle) {
                if (currentTurn > 4 * cycle) {
                    bool flag = true;
                    for (int s = 0; s < 2; ++s) {
                        for (int t = 0; t < 2; ++t) {
                            for (int i = 1; i <= 4 * cycle; ++i)if (hasDestroyBlock[s][t][currentTurn - i])flag = false;
                            for (int i = 1; i <= 4 * cycle - cycle; ++i) {
                                if (previousActions[currentTurn - i][s][t] !=
                                    previousActions[currentTurn - i - cycle][s][t])
                                    flag = false;
                            }
                            int x = 0, y = 0;
                            for (int i = 1; i <= cycle; ++i) {
                                if (ActionIsMove(previousActions[currentTurn - i][s][t])) {
                                    x += dx[previousActions[currentTurn - i][s][t]];
                                    y += dy[previousActions[currentTurn - i][s][t]];
                                }
                            }
                            if (x != 0 || y != 0)flag = false;
                        }
                    }
                    if (flag)return previousActions[currentTurn - cycle][side][tank];
                }
            }
            return Invalid;
        }
    };

    TankField *field;

    // 内部函数
    namespace Internals {
        Json::Reader reader;
#ifdef _BOTZONE_ONLINE
        Json::FastWriter writer;
#else
        Json::StyledWriter writer;
#endif

        void _processRequestOrResponse(Json::Value &value, bool isOpponent) {
            if (value.isArray()) {
                if (!isOpponent) {
                    for (int tank = 0; tank < tankPerSide; tank++)
                        field->nextAction[field->mySide][tank] = (Action) value[tank].asInt();
                } else {
                    for (int tank = 0; tank < tankPerSide; tank++)
                        field->nextAction[1 - field->mySide][tank] = (Action) value[tank].asInt();
                    field->DoAction();
                }
            } else {
                // 是第一回合，裁判在介绍场地
                int hasBrick[3], hasWater[3], hasSteel[3];
                for (int i = 0; i < 3; i++) {
                    hasWater[i] = value["waterfield"][i].asInt();
                    hasBrick[i] = value["brickfield"][i].asInt();
                    hasSteel[i] = value["steelfield"][i].asInt();
                }
                field = new TankField(hasBrick, hasWater, hasSteel, value["mySide"].asInt());
            }
        }

        // 请使用 SubmitAndExit 或者 SubmitAndDontExit
        void _submitAction(Action tank0, Action tank1, string debug = "", string data = "", string globaldata = "") {
            Json::Value output(Json::objectValue), response(Json::arrayValue);
            response[0U] = tank0;
            response[1U] = tank1;
            output["response"] = response;
            if (!debug.empty())
                output["debug"] = debug;
            if (!data.empty())
                output["data"] = data;
            if (!globaldata.empty())
                output["globaldata"] = globaldata;
            cout << writer.write(output) << endl;
        }
    }

    // 从输入流（例如 cin 或者 fstream）读取回合信息，存入 TankField，并提取上回合存储的 data 和 globaldata
    // 本地调试的时候支持多行，但是最后一行需要以没有缩进的一个"}"或"]"结尾
    void ReadInput(istream &in, string &outData, string &outGlobalData) {
        Json::Value input;
        string inputString;
        do {
            getline(in, inputString);
        } while (inputString.empty());
#ifndef _BOTZONE_ONLINE
        // 猜测是单行还是多行
        char lastChar = inputString[inputString.size() - 1];
        if (lastChar != '}' && lastChar != ']') {
            // 第一行不以}或]结尾，猜测是多行
            string newString;
            do {
                getline(in, newString);
                inputString += newString;
            } while (newString != "}" && newString != "]");
        }
#endif
        Internals::reader.parse(inputString, input);

        if (input.isObject()) {
            Json::Value requests = input["requests"], responses = input["responses"];
            if (!requests.isNull() && requests.isArray()) {
                int i, n = requests.size();
                for (i = 0; i < n; i++) {
                    Internals::_processRequestOrResponse(requests[i], true);
                    if (i < n - 1)
                        Internals::_processRequestOrResponse(responses[i], false);
                }
                outData = input["data"].asString();
                outGlobalData = input["globaldata"].asString();
                return;
            }
        }
        Internals::_processRequestOrResponse(input, true);
    }

    // 提交决策并退出，下回合时会重新运行程序
    void SubmitAndExit(Action tank0, Action tank1, string debug = "", string data = "", string globaldata = "") {
        Internals::_submitAction(tank0, tank1, debug, data, globaldata);
#ifndef _BOTZONE_ONLINE
        std::cerr << cnt << endl;
#endif
        exit(0);
    }

    // 提交决策，下回合时程序继续运行（需要在 Botzone 上提交 Bot 时选择“允许长时运行”）
    // 如果游戏结束，程序会被系统杀死
    void SubmitAndDontExit(Action tank0, Action tank1) {
        Internals::_submitAction(tank0, tank1);
        field->nextAction[field->mySide][0] = tank0;
        field->nextAction[field->mySide][1] = tank1;
        cout << ">>>BOTZONE_REQUEST_KEEP_RUNNING<<<" << endl;
    }

    struct DecisionTree {
        const int side, tank;
        clock_t endTime;
        static const int maxDepth = 4;

        double CountDown() {
            return (endTime - clock()) * 1.0 / CLOCKS_PER_SEC;
        }

        static constexpr Action acts[2][9] = {
                {DownShoot, Down, Stay, Left, Right, LeftShoot, RightShoot, Up,   UpShoot},
                {UpShoot,   Up,   Stay, Left, Right, LeftShoot, RightShoot, Down, DownShoot}
        };

        inline int LessStepIsBetter(int val) {
//            if (std::abs(val) >= (int) 1e6)return val - 1;
            return val - 1;
        }

        int EstimateCross(Action act0, Action act1) {
            Action pattern = field->GetPattern(!side, tank);
            for (auto act2:acts[!side]) {
                if (pattern != Invalid && pattern != act2)continue;
                if (field->ActionIsValid(!side, tank, act2)) {
                    field->nextAction[side][tank] = act0;
                    field->nextAction[!side][!tank] = act1;
                    field->nextAction[!side][tank] = act2;
                    field->nextAction[side][!tank] = Stay;
                    field->DoAction();
                    int ret = (int) 1e8;
                    if (field->CrossShoot(!side, !tank))ret = 1;
                    if (field->CrossShoot(!side, tank))ret = 1;
                    if (field->CrossShoot(side, tank))ret = (int) -1e9;
                    if (!field->tankAlive[side][tank])ret = (int) -1e9;
                    if (!field->tankAlive[!side][tank])ret = 1;
                    field->Revert();
                    if (ret < 0)return ret;
//                    if (field->WillKill(!side, tank, act2, side, tank, act0))return (int) -1e8;
//                    if (field->WillKill(side, tank, act0, !side, tank, act2))return (int) 0;
                }
            }
            return 0;
        }

        int table[9][9];

        pair<pair<int, Action>, Action> MinMax(int depth = 0, int alpha = (int) 1e9) {
            ++cnt;
            GameResult result = field->GetGameResult(side, tank);
            if (result == side)return make_pair(make_pair((int) 1e9, Invalid), Invalid);
            if (result == !side)return make_pair(make_pair((int) -1e9, Invalid), Invalid);
            if (result == Draw)return make_pair(make_pair(0, Invalid), Invalid);
            if (!field->tankAlive[side][tank])return make_pair(make_pair((int) -1e8, Stay), Stay);
            if (field->CrossShoot(side, tank))return make_pair(make_pair((int) -1e8, Stay), Stay);
            if (depth >= maxDepth) return make_pair(make_pair(field->EstimateAttack(side, tank), Invalid), Invalid);
            int beta = (int) -150000, secbeta = (int) -150000;
            Action act = Invalid, secact = Invalid;
            Action pattern = field->GetPattern(!side, !tank);
            if (depth <= 3) {// quick judge
                for (auto act0:acts[side]) {
                    if (field->ActionIsValid(side, tank, act0)) {
                        field->nextAction[side][tank] = act0;
                        int x = field->getDirection(!side, !tank);
                        field->nextAction[!side][!tank] = Stay;
                        if (depth == 0 && pattern != Invalid)field->nextAction[!side][!tank] = pattern;
                        field->nextAction[side][!tank] = Stay;
                        field->nextAction[!side][tank] = Stay;
                        field->DoAction();
                        GameResult result = field->GetGameResult(side, tank);
                        int tmp = beta;
                        if (result == side)tmp = (int) 1e9;
                        else if (result == !side);
                        else if (result == Draw);
                        field->Revert();
                        tmp = LessStepIsBetter(tmp);
                        if (depth == 0)tmp += EstimateCross(act0, Stay);
                        if (tmp > beta) {
                            secbeta = beta;
                            beta = tmp;
                            secact = act;
                            act = act0;
                        } else if (tmp > secbeta) {
                            secbeta = tmp;
                            secact = act0;
                        }
                    }
                }
            }
            for (auto act0:acts[side]) {
                if (beta >= alpha)break;
                if (field->ActionIsValid(side, tank, act0)) {
                    int gamma = (int) 1e9;
                    if (depth <= 3) {// quick judge
                        for (auto act1:acts[!side]) {
                            if (depth == 0 && pattern != Invalid && pattern != act1)continue;
                            if (field->ActionIsValid(!side, !tank, act1)) {
                                field->nextAction[side][tank] = act0;
                                field->nextAction[!side][!tank] = act1;
                                field->nextAction[side][!tank] = Stay;
                                field->nextAction[!side][tank] = Stay;
                                field->DoAction();
                                GameResult result = field->GetGameResult(side, tank);
                                if (result == side);
                                else if (result == !side)gamma = min(gamma, (int) -1e9);
                                else if (result == Draw)gamma = min(gamma, 0);
                                else if (!field->tankAlive[side][tank])gamma = min(gamma, (int) -1e8);
                                else if (field->CrossShoot(side, tank))gamma = min(gamma, (int) -1e8);
                                field->Revert();
                            }
                        }
                    }
                    for (auto act1:acts[!side]) {
                        if (gamma <= beta)break;
                        if (depth == 0 && pattern != Invalid && pattern != act1)continue;
                        if (field->ActionIsValid(!side, !tank, act1)) {
                            field->nextAction[side][tank] = act0;
                            field->nextAction[!side][!tank] = act1;
                            field->nextAction[side][!tank] = Stay;
                            field->nextAction[!side][tank] = Stay;
                            field->DoAction();
                            int tmp = MinMax(depth + 1, gamma).first.first;
                            field->Revert();
                            if (depth == 0)tmp += EstimateCross(act0, act1);
//                            if (depth == 0)table[act0 + 1][act1 + 1] = tmp;
                            gamma = min(gamma, tmp);
                        }
                    }
                    if (gamma > beta) {
                        secbeta = beta;
                        beta = gamma;
                        secact = act;
                        act = act0;
                    } else if (gamma > secbeta) {
                        secbeta = gamma;
                        secact = act0;
                    }
                }
            }
            return make_pair(make_pair(LessStepIsBetter(beta), act), secact);
        }

        Action Defense() {
            Action act = Invalid;
            int mn = (int) 1e9;
            int count[9]{0};
//            if (field->CanTankShootEachOther(side, tank, !side, tank) &&
//                field->CanTankShootEachOther(side, tank, !side, !tank))
//                return Stay;
            for (auto act0:acts[side]) {
                if (field->ActionIsValid(side, tank, act0)) {
                    bool flag = true;
                    for (auto act1:acts[!side]) {
//                        if (!flag)break;
                        if (field->ActionIsValid(!side, !tank, act1)) {
                            field->nextAction[side][tank] = act0;
                            field->nextAction[!side][!tank] = act1;
                            field->nextAction[side][!tank] = Stay;
                            field->nextAction[!side][tank] = Stay;
                            field->DoAction();
                            bool tmp = field->Defensible(side, tank);
                            field->Revert();
                            tmp &= EstimateCross(act0, Stay) >= 0;
                            if (tmp)++count[act0 + 1];
                            table[act0 + 1][act1 + 1] = tmp;
                            if (!tmp)flag = false;
                        }
                    }
                    field->nextAction[side][tank] = act0;
                    field->nextAction[!side][!tank] = Stay;
                    field->nextAction[side][!tank] = Stay;
                    field->nextAction[!side][tank] = Stay;
                    field->DoAction();
                    field->InitDistance(side, tank);
                    if (flag && field->dis[side][tank][baseY[side]][baseX[side]] < mn) {
                        act = act0;
                        mn = field->dis[side][tank][baseY[side]][baseX[side]];
                    }
                    field->Revert();
                }
            }
            if (act == Invalid) {
                int mx = -1;
                for (auto act0:acts[side]) {
                    if (field->ActionIsValid(side, tank, act0)) {
                        if (count[act0 + 1] > mx) {
                            mx = count[act0 + 1];
                            act = act0;
                        }
                    }
                }
            }
            return act;
        }

        void DebugTable() {
#ifndef _BOTZONE_ONLINE
            printf("%12c", ' ');
            for (auto act1:acts[!side]) {
                if (field->ActionIsValid(!side, !tank, act1)) {
                    printf("%12s", ActionToString(act1));
                }
            }
            puts("");
            for (auto act0:acts[side]) {
                if (field->ActionIsValid(side, tank, act0)) {
                    printf("%12s", ActionToString(act0));
                    for (auto act1:acts[!side]) {
                        if (field->ActionIsValid(!side, !tank, act1)) {
                            printf("%12d", table[act0 + 1][act1 + 1]);
                        }
                    }
                    puts("");
                }
            }
            puts("===============================================================================================================");
#endif
        }

        pair<Action, Action> GetAction() {
            auto[pa, secact] = MinMax();
            auto[value, act] = pa;
            debug += ' ' + std::to_string(value) + ' ';
//            if (value <= -100000 && (act == Invalid || field->Defensible(side, tank))) {
//                Action defense = Defense();
//                DebugTable();
//                return Defense();
//            }
            if (act == Invalid)act = Stay;
            if (secact == Invalid)secact = Stay;
            return make_pair(act, secact);
        }

        DecisionTree(int tank, clock_t endTime) : endTime(endTime), side(TankGame::field->mySide), tank(tank) {}
    };

    void SubmitAction() {
        int TIME = (field->currentTurn == 1 ? 2 : 1) * CLOCKS_PER_SEC;
        auto tree0 = new DecisionTree(0, startTime + (int) (0.49 * TIME));
        auto tree1 = new DecisionTree(1, startTime + (int) (0.99 * TIME));
        auto[act0, secact0] = tree0->GetAction();
        auto[act1, secact1] = tree1->GetAction();
        if (field->MayKill(field->mySide, 0, act0, field->mySide, 1, act1))act0 = secact0;
        if (field->MayKill(field->mySide, 1, act1, field->mySide, 0, act0))act1 = secact1;
        if (field->MayStack(field->mySide, 0, act0, field->mySide, 1, act1))act0 = secact0;
        if (field->MayStack(field->mySide, 1, act1, field->mySide, 0, act0))act1 = secact1;
        debug += std::to_string((clock() - startTime) * 1.0 / CLOCKS_PER_SEC);
        SubmitAndExit(act0, act1, debug);
    }
}


int RandBetween(int from, int to) {
    return rand() % (to - from) + from;
}

TankGame::Action RandAction(int tank) {
    while (true) {
        auto act = (TankGame::Action) RandBetween(TankGame::Stay, TankGame::LeftShoot + 1);
        if (TankGame::field->ActionIsValid(TankGame::field->mySide, tank, act))
            return act;
    }
}

int main() {
    srand((unsigned) time(nullptr));

    string data, globaldata;
    TankGame::ReadInput(cin, data, globaldata);
    startTime = clock();
    TankGame::field->DebugPrint();
    TankGame::SubmitAction();
}