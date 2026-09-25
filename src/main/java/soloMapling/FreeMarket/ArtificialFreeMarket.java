package soloMapling.FreeMarket;

import org.gms.client.Client;
import org.gms.client.Character;
import org.gms.client.Job;
import org.gms.net.server.Server;
import org.gms.server.maps.HiredMerchant;
import org.gms.server.maps.PlayerShop;
import org.gms.server.maps.PlayerShopItem;
import org.gms.server.maps.MapleMap;
import soloMapling.server.ExecutorServiceManager;
import org.gms.util.PacketCreator;

import java.awt.*;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.concurrent.ConcurrentHashMap;
import java.util.Set;

import static soloMapling.ArtificialPlayer.BotCustomization.getRandomChairId;
import static soloMapling.ArtificialPlayer.BotCustomization.getRandomStorePermitId;
import soloMapling.ArtificialPlayer.BotGeneration;

import static soloMapling.ArtificialPlayer.BotGeneration.createBotPollReadiness;
import static soloMapling.server.ExecutorServiceManager.runAsync;
import static soloMapling.ArtificialPlayer.BotMovementSystem.MovementCommands.botSitChair;
import static soloMapling.ArtificialPlayer.BotMovementSystem.MovementCommands.microTurnAround;
import static soloMapling.DebugUtilities.debugprint;
import static soloMapling.FreeMarket.ArtificialShopGenerator.applyAdditionalShopMods;
import static soloMapling.FreeMarket.ArtificialShopGenerator.applyCheapSaleDiscount;
import static soloMapling.FreeMarket.ArtificialShopGenerator.applyQuittingSaleDiscount;
import static soloMapling.FreeMarket.ArtificialShopGenerator.buyoutSomeItems;
import static soloMapling.FreeMarket.ArtificialShopGenerator.setOneMesoShop;
import static soloMapling.FreeMarket.ArtificialShopGenerator.generateShop;
import static soloMapling.FreeMarket.ArtificialShopGenerator.generateSecondaryShop;

import static soloMapling.FreeMarket.FMEconomyManager.getTierForRoom;
import static soloMapling.FreeMarket.FMEconomyManager.isHotRoom;
import static soloMapling.FreeMarket.FMShopTypeManager.selectHotRoomShopType;
import static soloMapling.FreeMarket.FMShopDescriptionManager.appendRoomNumber;
import static soloMapling.FreeMarket.FMShopDescGen.getRandomShopOwnerIGN;
import static soloMapling.FreeMarket.FMShopDescriptionManager.setMerchantDescription;
import static soloMapling.FreeMarket.FMShopDescriptionManager.appendMerchantDescription;
import static soloMapling.FreeMarket.FMShopInfoManager.getRegionByMapId;
import static soloMapling.FreeMarket.FMShopTypeManager.getSecondaryShopItemTypes;
import static soloMapling.FreeMarket.FMShopTypeManager.selectShopTypeWeightedProbability;

import static soloMapling.FreeMarket.HiredMerchantArtificial.shopTypes.*;
import static soloMapling.server.ExecutorServiceManager.getExecutorService;
import static soloMapling.server.ExecutorServiceManager.getScheduledExecutorService;
import static soloMapling.server.SoloMaplingUtilities.chance;
import static soloMapling.server.SoloMaplingUtilities.getMapleMapById;

public class ArtificialFreeMarket {

    static List<Integer> hiredMerchantsList = Arrays.asList(5030000, 5030001, 5030002, 5030004, 5030008, 5030010); // 5030012 - tiki torch
    private static final Random random = new Random();
    public static FMShopInfoManager fmInfo = new FMShopInfoManager();

    /**
     * Artificial Free Market lifecycle:
     * one complete generated market lives for 24 hours, then only our
     * artificial shops are removed and the market is generated again.
     */
    private static final long FM_REFRESH_INTERVAL_HOURS = 24L;
    private static final int FM_SHOP_COLLISION_RADIUS = 40;
    private static final AtomicBoolean fmRefreshSchedulerStarted = new AtomicBoolean(false);
    private static final AtomicInteger fmGeneration = new AtomicInteger(0);
    private static final Object FM_REFRESH_LOCK = new Object();

    // Only shops/bots created by SoloMapling are stored here. Real player shops
    // are never added, so a refresh cannot delete them.
    private static final Set<PlayerShop> artificialPlayerShops = ConcurrentHashMap.newKeySet();
    private static final Set<Character> artificialShopBots = ConcurrentHashMap.newKeySet();
    private static final Set<HiredMerchantArtificial> artificialMerchants = ConcurrentHashMap.newKeySet();
    private static final ConcurrentHashMap<HiredMerchantArtificial, Integer> artificialMerchantChannelKeys =
            new ConcurrentHashMap<>();

    // Prevents duplicate generation when the same FM region is triggered more than once.
    private static final Set<String> reservedGenerationSpots = ConcurrentHashMap.newKeySet();

    public static void populateFreeMarketSpot(Client c) {
        spawnHiredMerchantStore(c.getPlayer().getMapId(), c.getPlayer().getPosition());
    }

    public static void populateFreeMarketFull() {
        List<String> regions = List.of("henesys", "ludi", "perion", "elnath");
        int generation = fmGeneration.get();
        reservedGenerationSpots.clear();
        for (String region : regions) {
            populateFreeMarketRegion(region, generation);
        }
    }

    public static void populateFreeMarketRegion(String region) {
        populateFreeMarketRegion(region, fmGeneration.get());
    }

    private static void populateFreeMarketRegion(String region, int generation) {
        for (int mapId : fmInfo.getRegionFMMapId(region)) {
            ExecutorServiceManager.runAsync(() -> populateFreeMarketRoom(mapId, generation));
        }
    }

    private static void populateFreeMarketRoom(int mapId, int generation) {
        if (!isCurrentGeneration(generation)) {
            return;
        }

        String region = getRegionByMapId(mapId);
        debugprint("Populating room: ", mapId);

        List<Point> positions = fmInfo.getRegionFMSpots(region);
        AtomicInteger delayCounter = new AtomicInteger(0);
        double hiredMerchantChance = getHiredMerchantChance(mapId);

        for (Point position : positions) {
            if (!isCurrentGeneration(generation)) {
                return;
            }
            if (chance(2)) {
                continue;
            }

            // Reserve the configured spot before scheduling asynchronous work.
            // This closes the race where two population calls both see an empty spot.
            if (!reserveGenerationSpot(mapId, position, generation)) {
                continue;
            }

            if (Math.random() < hiredMerchantChance) {
                ExecutorServiceManager.runAsync(() -> {
                    if (isCurrentGeneration(generation)) {
                        spawnHiredMerchantStore(mapId, position, generation);
                    }
                });
            } else {
                int delay = delayCounter.getAndIncrement() * 200;
                getScheduledExecutorService().schedule(
                        () -> createBotShopAtLocation(position, mapId, generation),
                        delay, TimeUnit.MILLISECONDS);
            }
        }
    }

//    public static void populateFreeMarket(String region, int mapId) {
//        for (Point position : fmInfo.getRegionFMSpots(region)) {
//            ExecutorServiceManager.getExecutorService().execute(() ->
//                    spawnHiredMerchantStore(mapId, position));
//        }
//    }


    private static void spawnHiredMerchantStore(int mapId, Point position) {
        spawnHiredMerchantStore(mapId, position, fmGeneration.get());
    }

    private static void spawnHiredMerchantStore(int mapId, Point position, int generation) {
        if (!isCurrentGeneration(generation) || calculateSkippedSpot(mapId)) {
            return;
        }

        MapleMap map = getMapleMapById(mapId);
        if (hasShopNearPosition(map, position, FM_SHOP_COLLISION_RADIUS)) {
            debugprint("Skipping occupied FM spot: " + mapId + " " + position);
            return;
        }

        int world = 0;
        int channel = 1;

        int ownerId = 20000 + random.nextInt(10001);
        String ownerName = getRandomShopOwnerIGN();
        String description = "";

        int shop_item_id = hiredMerchantsList.get(random.nextInt(hiredMerchantsList.size())); // 5030000;
        Client cm = Client.createMock();
        Character newchar = Character.getDefault(cm);
        newchar.setPosition(position);
        newchar.setMap(Server.getInstance().getChannel(world, channel).getMapFactory().getMap(mapId));

        generateHiredMerchantShopData(newchar, ownerName, ownerId, description, shop_item_id, mapId);

        addMerchantToChannel(newchar);
    }

    private static HiredMerchantArtificial generateHiredMerchantShopData(Character newchar, String ownerName, int ownerId, String description, int shop_item_id, int mapId) {
        HiredMerchantArtificial newMerch = createMerchantObject(newchar, ownerName, ownerId, description, shop_item_id);

        String tier = getTierForRoom(mapId);

        newMerch.setTier(tier);
        newMerch.setMapId(mapId);

        /* todo add all scrolls weps for class type shops */
        boolean hotRoom = isHotRoom(mapId);
        HiredMerchantArtificial.shopTypes primaryShopType = hotRoom
                ? selectHotRoomShopType()
                : selectShopTypeWeightedProbability();
        newMerch.setPrimary(primaryShopType);

        generatePrimaryShop(primaryShopType, newMerch);

        if (hotRoom) {
            generateBonusEquipsForHotRoom(newMerch);
            generateSecondaryShopItems(newMerch);
            generateSecondaryShopItems(newMerch);
            fillHotRoomToMinimum(newMerch);
        } else {
            generateSecondaryShopItems(newMerch);
            generateTertiaryBackupShop(newMerch);
        }

        new FMShopDescriptionManager().generateDescription(newMerch);

        // special rules shop modifications
        applyAdditionalShopMods(newMerch);
        buyoutSomeItems(newMerch);
        applySpecialShopType(newMerch);

        appendRoomNumber(newMerch);
        return newMerch;
    }

    private static void generatePrimaryShop(HiredMerchantArtificial.shopTypes choice, HiredMerchantArtificial merchant) {
        /*
        1. Class Oriented
            Common
            Warr
            Mage
            Bow
            Thief
                Stars
            Pirate
        2. Other Oriented
            Pot
            Scroll
            Dark Scroll
            Mastery
            Chair
            ETC

         Mix
            1. Class Oriented + 2. Other Oriented (Mini)
         */


        Runnable action = switch (choice) {
            case Warrior -> () -> {
                generateShop(merchant, Job.WARRIOR);
            };
            case Mage -> () -> {
                generateShop(merchant, Job.MAGICIAN);
            };
            case Bowman -> () -> {
                generateShop(merchant, Job.BOWMAN);
            };
            case Thief -> () -> {
                generateShop(merchant, Job.THIEF);
            };
            case Common -> () -> {
                generateShop(merchant, Job.BEGINNER);
            };
            case Pirate -> () -> {
                debugprint("Generating pirate shop");
                generateShop(merchant, Job.BEGINNER);
                // generatePirateEquipShop(merchant);
            };
            case Scroll -> () -> {
                repeatAction(3, () -> generateSecondaryShop(merchant, Scroll)); // generateScrollShop(newchar, tier));
            };
            case DarkScroll -> () -> {
                repeatAction(3, () -> generateSecondaryShop(merchant, DarkScroll)); // generateDarkScrollShop(newchar, tier));
            };
            case Potion -> () -> {
                repeatAction(3, () -> generateSecondaryShop(merchant, Potion)); // generateUseablesShop(newchar, tier));
            };
            case ETC -> () -> {
                repeatAction(3, () -> generateSecondaryShop(merchant, ETC)); // generateETCShop(newchar, tier));
            };
            case Chair -> () -> {
                repeatAction(5, () -> generateSecondaryShop(merchant, Chair)); // generateChairShop(newchar, tier));
            };
            case Mastery -> () -> {
                repeatAction(3, () -> generateSecondaryShop(merchant, Mastery)); // generateMasteryShop(newchar, tier));
            };
            default -> throw new IllegalArgumentException("Invalid shop type: " + choice);
        };
        action.run();
    }

    private static void generateSecondaryShopItems(HiredMerchantArtificial merchant) {
        // Randomly select 1 or 2 items based on weights
        List<HiredMerchantArtificial.shopTypes> selectedItems = getSecondaryShopItemTypes(); // getWeightedSelection(itemWeights);
        merchant.setSecondary(selectedItems.getFirst());

        for (HiredMerchantArtificial.shopTypes itemType : selectedItems) {
            applySecondaryShopItems(merchant, itemType);
        }
    }

    private static void applySecondaryShopItems(HiredMerchantArtificial merchant, HiredMerchantArtificial.shopTypes item) {
        switch (item) {
            case Potion:
                generateSecondaryShop(merchant, Potion);
                break;
            case Scroll:
                generateSecondaryShop(merchant, Scroll);
                break;
            case DarkScroll:
                generateSecondaryShop(merchant, DarkScroll);
                break;
            case Mastery:
                generateSecondaryShop(merchant, Mastery);
                break;
            case Chair:
                generateSecondaryShop(merchant, Chair);
                break;
            case ETC:
                generateSecondaryShop(merchant, ETC);
                break;
            default:
                debugprint("Unknown item: " + item);
        }
    }

    private static void generateTertiaryBackupShop(HiredMerchantArtificial merchant) {
        if (merchant.getItems().size() < 5) {
            int choice = random.nextInt(5); // Random Equip Common thru Pirate
            HiredMerchantArtificial.shopTypes tertiary = HiredMerchantArtificial.shopTypes.values()[choice];
            merchant.setTertiary(tertiary);
            generatePrimaryShop(tertiary, merchant);
        }
    }

    private static final Job[] CLASS_JOBS = {Job.WARRIOR, Job.MAGICIAN, Job.BOWMAN, Job.THIEF, Job.BEGINNER};

    private static void generateBonusEquipsForHotRoom(HiredMerchantArtificial merchant) {
        Job bonusClass = CLASS_JOBS[random.nextInt(CLASS_JOBS.length)];
        generateShop(merchant, bonusClass);
    }

    private static void fillHotRoomToMinimum(HiredMerchantArtificial merchant) {
        int attempts = 0;
        while (merchant.getItems().size() < 10 && attempts < 3) {
            Job fillClass = CLASS_JOBS[random.nextInt(CLASS_JOBS.length)];
            generateShop(merchant, fillClass);
            attempts++;
        }
    }

    private static HiredMerchantArtificial createMerchantObject(Character newchar, String ownerName, int ownerId, String description, int shopItemId) {
        // STEP 1 - CREATE MERCHANT OBJECT
        HiredMerchantArtificial merchant = new HiredMerchantArtificial(newchar, description, shopItemId, ownerId, ownerName);
        newchar.setHiredMerchant(merchant);
        newchar.getWorldServer().registerHiredMerchant(merchant);
        newchar.getWorldServer().getChannel(1).addHiredMerchant(newchar.getId(), merchant);
        artificialMerchants.add(merchant);
        artificialMerchantChannelKeys.put(merchant, newchar.getId());
        return merchant;
    }

    private static HiredMerchant addMerchantToChannel(Character newchar) {
        // Step 3
        HiredMerchant merchant = newchar.getHiredMerchant();
        newchar.setHasMerchant(true);
        merchant.setOpen(true);
        merchant.getMap().addMapObject(merchant);
        newchar.setHiredMerchant(null);
        merchant.getMap().broadcastMessage(PacketCreator.spawnHiredMerchantBox(merchant));
        return merchant;
    }

    private static double getHiredMerchantChance(int mapId) {
        return switch (mapId) {
            case 910000001 -> 0.90;
            case 910000002 -> 0.80;
            case 910000007 -> 0.70;
            case 910000003 -> 0.60;
            default -> 0.40;
        };
    }

    private static boolean calculateSkippedSpot(int mapId) {
        // Map to store regions and their probabilities
        Map<String, Double> regionProbabilities = Map.of(
                "henesys", 0.002,
                "ludi", 0.04,
                "perion", 0.10,
                "elnath", 0.15
        );

        // Iterate through the map to find the matching region and apply the probability
        for (Map.Entry<String, Double> entry : regionProbabilities.entrySet()) {
            if (fmInfo.getRegionFMMapId(entry.getKey()).contains(mapId)) {
                return Math.random() < entry.getValue();
            }
        }

        return false; // Default case
    }

    private static void applySpecialShopType(HiredMerchantArtificial merchant) {
        Random random = new Random();
        int roll = random.nextInt(10_000);
        if (roll == 0) { // 1 in 10,000 chance
            setOneMesoShop(merchant);
            setMerchantDescription(merchant, " 1 MESO SHOP!!!");
            return;
        }
        if (roll < 100) { // 100 in 10,000 chance (1%)
            // Quitting Sale
            applyQuittingSaleDiscount(merchant);
            appendMerchantDescription(merchant, " QUITTING SALE");
            return;
        }
        if (roll < 800) { // 800 in 10,000 chance (7%)
            applyCheapSaleDiscount(merchant);
            appendMerchantDescription(merchant, " Cheap");
            return;
        }
    }

    // doesnt work
    public static void destroyAllShops(Client c) {
        debugprint("Destroy all shops");
        c.getWorldServer().getChannel(1).closeAllMerchants();
//        c.getChannelServer().closeAllMerchants();
    }

    private static void repeatAction(int times, Runnable action) {
        for (int i = 0; i < times; i++) {
            action.run();
        }
    }

    /////////////////////////////////

    // Bot Store Permits

    public static void BotPlayerStorePermit(Character fakechar) {
        String desc = "Test";
        Integer shopItemId = getRandomStorePermitId();
        MapleMap map = fakechar.getMap();
        if (map == null || hasShopNearPosition(map, fakechar.getPosition(), FM_SHOP_COLLISION_RADIUS)) {
            return;
        }

        PlayerShop ps = new PlayerShop(fakechar, desc, shopItemId);
        fakechar.setPlayerShop(ps);
        map.addMapObject(ps);
        artificialPlayerShops.add(ps);
        artificialShopBots.add(fakechar);

        HiredMerchantArtificial hma = generateHiredMerchantShopData(fakechar, fakechar.getName(), fakechar.getId(), desc, 5030000, fakechar.getMapId());
        String desc2 = hma.getDescription();
        ps.setDescription(desc2);
        List<PlayerShopItem> premadeShop = hma.getItems();
        ps.setItems(premadeShop);

        // open shop on map
        PlayerShop fakecharplayershop = fakechar.getPlayerShop();
        fakecharplayershop.setOpen(true);


    }

//    public static void testchoice() {
//        // Create a map to store the counts of each choice
//        Map<Integer, Integer> choiceCounts = new HashMap<>();
//
//        // Initialize counts for each choice to 0
//        for (int key : shopTypeWeights.keySet()) {
//            choiceCounts.put(key, 0);
//        }
//
//        // Run the selection process 1000 times
//        for (int i = 0; i < 1000; i++) {
//            int choice = selectShopTypeWeightedProbability();
//            choiceCounts.put(choice, choiceCounts.getOrDefault(choice, 0) + 1);
//        }
//
//        // Print the results
//        debugprint("Results after 1000 runs:");
//        for (Map.Entry<Integer, Integer> entry : choiceCounts.entrySet()) {
//            debugprint("Choice " + entry.getKey() + ": " + entry.getValue() + " times");
//        }
//    }

    public static void main(String[] args) {
//        testchoice();
    }

////    private static final int THREAD_POOL_SIZE = Math.min(Runtime.getRuntime().availableProcessors() * 8, 30);
////    private static final ExecutorService executor = Executors.newFixedThreadPool(THREAD_POOL_SIZE);
//    private static final ScheduledExecutorService scheduler = Executors.newScheduledThreadPool(1);

    public static void createBotShopAtLocation(Point position, int mapId) {
        createBotShopAtLocation(position, mapId, fmGeneration.get());
    }

    private static void createBotShopAtLocation(Point position, int mapId, int generation) {
        getExecutorService().submit(() -> {
            if (!isCurrentGeneration(generation)) {
                return;
            }

            MapleMap map = getMapleMapById(mapId);
            if (hasShopNearPosition(map, position, FM_SHOP_COLLISION_RADIUS)) {
                debugprint("Skipping occupied FM bot-shop spot: " + mapId + " " + position);
                return;
            }

            debugprint("Making shop at: " + mapId + ", " + position);
            Character fakechar2 = createBotPollReadiness(position, mapId);
            if (fakechar2 == null) {
                System.err.println("Bot not ready after 3 seconds, skipping store");
                return;
            }

            artificialShopBots.add(fakechar2);

            getScheduledExecutorService().schedule(() -> runAsync(() -> {
                if (!isCurrentGeneration(generation)) {
                    BotGeneration.removeBotFromServer(fakechar2);
                    artificialShopBots.remove(fakechar2);
                    return;
                }

                MapleMap currentMap = fakechar2.getMap();
                if (currentMap == null || hasShopNearPosition(currentMap, fakechar2.getPosition(), FM_SHOP_COLLISION_RADIUS)) {
                    BotGeneration.removeBotFromServer(fakechar2);
                    artificialShopBots.remove(fakechar2);
                    return;
                }

                BotPlayerStorePermit(fakechar2);

                if (fakechar2.getPlayerShop() == null) {
                    BotGeneration.removeBotFromServer(fakechar2);
                    artificialShopBots.remove(fakechar2);
                    return;
                }

                if (Math.random() < 0.5) {
                    microTurnAround(fakechar2);
                }
                if (Math.random() < 0.4) {
                    getScheduledExecutorService().schedule(() -> {
                        if (isCurrentGeneration(generation)) {
                            botSitChair(fakechar2, getRandomChairId());
                        }
                    }, 500, TimeUnit.MILLISECONDS);
                }
            }), BotGeneration.SPAWN_CHOREOGRAPHY_MAX_MS, TimeUnit.MILLISECONDS);
        });
    }

    /** Starts the 24-hour artificial Free Market lifecycle. */
    public static void startFreeMarketRefreshScheduler() {
        if (!fmRefreshSchedulerStarted.compareAndSet(false, true)) {
            return;
        }

        long interval = FM_REFRESH_INTERVAL_HOURS * 60L * 60L * 1000L;
        getScheduledExecutorService().scheduleAtFixedRate(() -> {
            try {
                refreshFreeMarket();
            } catch (Throwable t) {
                System.err.println("[FreeMarket] 24-hour refresh failed:");
                t.printStackTrace();
            }
        }, interval, interval, TimeUnit.MILLISECONDS);
    }

    /**
     * Recreates the artificial Free Market as if the server had restarted.
     * Real player shops are deliberately not touched.
     */
    public static void refreshFreeMarket() {
        synchronized (FM_REFRESH_LOCK) {
            int newGeneration = fmGeneration.incrementAndGet();
            reservedGenerationSpots.clear();

            debugprint("Starting 24-hour Free Market refresh, generation=" + newGeneration);
            clearArtificialFreeMarket();
            populateFreeMarketFull();
            debugprint("24-hour Free Market refresh scheduled, generation=" + newGeneration);
        }
    }

    private static void clearArtificialFreeMarket() {
        for (PlayerShop shop : artificialPlayerShops) {
            try {
                MapleMap map = shop.getOwner() != null ? shop.getOwner().getMap() : null;
                if (map != null) {
                    map.broadcastMessage(PacketCreator.removePlayerShopBox(shop));
                    map.removeMapObject(shop);
                }
                shop.setOpen(false);
                if (shop.getOwner() != null && shop.getOwner().getPlayerShop() == shop) {
                    shop.getOwner().setPlayerShop(null);
                }
            } catch (Throwable t) {
                System.err.println("[FreeMarket] Failed to remove artificial PlayerShop:");
                t.printStackTrace();
            }
        }
        artificialPlayerShops.clear();

        for (HiredMerchantArtificial merchant : artificialMerchants) {
            try {
                MapleMap map = merchant.getMap();
                if (map != null) {
                    map.broadcastMessage(PacketCreator.removeHiredMerchantBox(merchant.getOwnerId()));
                    map.removeMapObject(merchant);
                }

                Integer channelKey = artificialMerchantChannelKeys.get(merchant);
                if (channelKey != null) {
                    Server.getInstance().getChannel(0, 1).removeHiredMerchant(channelKey, merchant);
                }
                Server.getInstance().getWorld(0).unregisterHiredMerchant(merchant);
            } catch (Throwable t) {
                System.err.println("[FreeMarket] Failed to remove artificial HiredMerchant:");
                t.printStackTrace();
            }
        }
        artificialMerchants.clear();
        artificialMerchantChannelKeys.clear();

        for (Character bot : artificialShopBots) {
            try {
                BotGeneration.removeBotFromServer(bot);
            } catch (Throwable t) {
                System.err.println("[FreeMarket] Failed to remove artificial FM bot " + bot.getId() + ":");
                t.printStackTrace();
            }
        }
        artificialShopBots.clear();
    }

    private static boolean isCurrentGeneration(int generation) {
        return fmGeneration.get() == generation;
    }

    private static boolean reserveGenerationSpot(int mapId, Point position, int generation) {
        if (!isCurrentGeneration(generation)) {
            return false;
        }
        return reservedGenerationSpots.add(spotKey(mapId, position));
    }

    private static String spotKey(int mapId, Point position) {
        return mapId + ":" + position.x + ":" + position.y;
    }

    private static boolean hasShopNearPosition(MapleMap map, Point position, int radius) {
        if (map == null || position == null) {
            return false;
        }

        double radiusSquared = (double) radius * radius;
        for (HiredMerchant merchant : map.getAllHiredMerchants()) {
            Point actual = merchant.getPosition();
            if (actual != null && actual.distanceSq(position) <= radiusSquared) {
                return true;
            }
        }

        for (PlayerShop shop : map.getAllPlayerShops()) {
            Point actual = shop.getPosition();
            if (actual != null && actual.distanceSq(position) <= radiusSquared) {
                return true;
            }
        }
        return false;
    }

}
