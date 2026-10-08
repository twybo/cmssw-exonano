#include <algorithm>
#include <memory>
#include <vector>
#include <cmath>
#include <limits>
#include <unordered_map>
#include <utility>

#include "FWCore/Framework/interface/Frameworkfwd.h"
#include "FWCore/Framework/interface/global/EDProducer.h"
#include "FWCore/Framework/interface/Event.h"
#include "FWCore/Framework/interface/MakerMacros.h"
#include "FWCore/MessageLogger/interface/MessageLogger.h"
#include "FWCore/Utilities/interface/Exception.h"
#include "FWCore/ParameterSet/interface/ParameterSet.h"
#include "FWCore/ParameterSet/interface/ConfigurationDescriptions.h"
#include "FWCore/ParameterSet/interface/ParameterSetDescription.h"

#include "DataFormats/PatCandidates/interface/IsolatedTrack.h"
#include "DataFormats/PatCandidates/interface/Muon.h"
#include "DataFormats/Candidate/interface/Candidate.h"
#include "DataFormats/TrackReco/interface/DeDxHitInfo.h"
#include "DataFormats/Common/interface/Association.h"
#include "DataFormats/Common/interface/Ref.h"
#include "DataFormats/Common/interface/Ptr.h"
#include "DataFormats/Provenance/interface/ProductID.h"
#include "DataFormats/NanoAOD/interface/FlatTable.h"
#include "DataFormats/SiPixelDetId/interface/PixelSubdetector.h"
#include "DataFormats/SiStripDetId/interface/SiStripDetId.h"
#include "DataFormats/TrackerCommon/interface/TrackerTopology.h"
#include "Geometry/Records/interface/TrackerTopologyRcd.h"

namespace {
  struct PairHash {
    size_t operator()(const std::pair<edm::ProductID, unsigned int>& p) const {
      // edm::ProductID has no std::hash specialization; hash its process/product indices directly.
      const size_t h1 = (static_cast<size_t>(p.first.processIndex()) << 16) | p.first.productIndex();
      return std::hash<size_t>()(h1) ^ (std::hash<unsigned int>()(p.second) << 1);
    }
  };

  // DeDxHitInfo stores the pixel cluster charge in electrons and the strip cluster charge in ADC counts, so the
  // two subdetectors need different conversions to MeV. These reproduce the RECO defaults MeVperADCPixel and
  // MeVperADCStrip (= 3.61e-06 * 265) in RecoTracker/DeDx/python/dedxEstimators_cff.py, which is where the
  // DeDxHitInfo collection read here is produced. They are neither an event product nor an EventSetup record, so
  // they have to be repeated; keep them in sync with that file.

  // Mean energy needed to create one electron-hole pair in silicon.
  constexpr float kMeVPerElectronHolePair = 3.61e-06f;
  // Strip readout gain: electrons per ADC count.
  constexpr float kElectronsPerADCStrip = 265.f;

  // Largest hit count representable in the uint8_t counter columns.
  constexpr size_t kMaxHitCount = std::numeric_limits<uint8_t>::max();

  bool isPixel(int subdet) {
    return subdet == PixelSubdetector::PixelBarrel || subdet == PixelSubdetector::PixelEndcap;
  }

  // Sensor-edge fiducial cuts, following EXO-19-006.

  bool isNearEdgeBPix(float localX, float localY) {
    bool found = false;
    if (localX > 0.79 || localX < -0.8)
      found = true;
    if (std::abs(localY) > 3.2)
      found = true;
    return found;
  }

  bool isNearEdgeFPix(float localX, float localY) {
    bool found = false;
    if (std::abs(localX) > 0.8)
      found = true;
    if (std::abs(localY) > 3.2)
      found = true;
    return found;
  }

  bool isNearEdgeTIB(float localX, float localY) {
    bool found = false;
    if (std::abs(localX) > 3.05)
      found = true;
    if (std::abs(localY) > 5.6)
      found = true;
    return found;
  }

  bool isNearEdgeTID(unsigned int ring, float localX, float localY) {
    bool found = false;
    if (ring == 1) {
      if (std::abs(localY) < 5.5)
        found = true;
      if ((localX < 0 && (localY - 7.41f * localX - 28.23f) > 0) ||
          (localX > 0 && (localY + 7.41f * localX - 28.23f) > 0))
        found = true;
    } else if (ring == 2) {
      if (std::abs(localY) < 4.35)
        found = true;
      if ((localX < 0 && (localY - 7.63f * localX - 37.2f) > 0) ||
          (localX > 0 && (localY + 7.47f * localX - 36.49f) > 0))
        found = true;
    } else if (ring == 3) {
      if (localY < -5.5 || localY > 5.45)
        found = true;
      if ((localX < 0 && (localY + 12.43f * localX + 44.6f) < 0) ||
          (localX > 0 && (localY - 12.51f * localX + 44.9f) < 0))
        found = true;
    } else {
      edm::LogWarning("MuonTrackDeDxTableProducer") << "No ring found for TID, check for error";
    }
    return found;
  }

  bool isNearEdgeTOB(float localX, float localY) {
    bool found = false;
    if (std::abs(localX) > 4.65)
      found = true;
    if (std::abs(localY) < 0.25 || std::abs(localY) > 9.2)
      found = true;
    return found;
  }

  bool isNearEdgeTEC(unsigned int ring, float localX, float localY) {
    bool found = false;
    if (ring == 1) {
      if (std::abs(localY) > 4.2)
        found = true;
      if ((localX < 0 && (localY - 7.49f * localX - 27.65f) > 0) ||
          (localX > 0 && (localY + 7.51f * localX - 27.68f) > 0))
        found = true;
    } else if (ring == 2) {
      if (std::abs(localY) > 4.35)
        found = true;
      if ((localX < 0 && (localY - 7.32f * localX - 35.7f) > 0) ||
          (localX > 0 && (localY + 7.45f * localX - 36.4f) > 0))
        found = true;
    } else if (ring == 3) {
      if (localY < -5.45 || localY > 5.5)
        found = true;
      if ((localX < 0 && (localY - 12.62f * localX - 45.24f) > 0) ||
          (localX > 0 && (localY + 12.46f * localX - 44.67f) > 0))
        found = true;
    } else if (ring == 4) {
      if (std::abs(localY) > 5.7)
        found = true;
      if ((localX < 0 && (localY - 17.53f * localX - 56.39f) > 0) ||
          (localX > 0 && (localY + 17.38f * localX - 55.8f) > 0))
        found = true;
    } else if (ring == 5) {
      if (std::abs(localY) > 7.3 || (localY > -0.82f && localY < -0.7f) || (localY > -1.1f && localY < -1.0f))
        found = true;
      if ((localX < 0 && (localY - 12.45f * localX - 67.1f) > 0) ||
          (localX > 0 && (localY + 12.65f * localX - 68.18f) > 0))
        found = true;
    } else if (ring == 6) {
      if (std::abs(localY) > 9.1 || (localY > -0.82f && localY < -0.75f) || (localY > -0.52f && localY < -0.35f))
        found = true;
      if ((localX < 0 && (localY - 17.41f * localX - 81.56f) > 0) ||
          (localX > 0 && (localY + 17.48f * localX - 81.81f) > 0))
        found = true;
    } else if (ring == 7) {
      if (std::abs(localY) > 10.15 || (localY > 0.4f && localY < 0.54f) || (localY > 0.68f && localY < 0.84f))
        found = true;
      if ((localX < 0 && (localY + 24.53f * localX + 97.35f) < 0) ||
          (localX > 0 && (localY - 24.88f * localX - 98.68f) < 0))
        found = true;
    } else {
      edm::LogWarning("MuonTrackDeDxTableProducer") << "No ring found for TEC, check for error";
    }
    return found;
  }

  // DetId::subdetId() in the tracker:
  //   1 = BPix, 2 = FPix, 3 = TIB, 4 = TID, 5 = TOB, 6 = TEC
  bool isHitNearEdge(const TrackerTopology& tTopo, DetId detId, float localX, float localY) {
    switch (detId.subdetId()) {
      case PixelSubdetector::PixelBarrel:
        return isNearEdgeBPix(localX, localY);
      case PixelSubdetector::PixelEndcap:
        return isNearEdgeFPix(localX, localY);
      case SiStripDetId::TIB:
        return isNearEdgeTIB(localX, localY);
      case SiStripDetId::TID:
        return isNearEdgeTID(tTopo.tidRing(detId), localX, localY);
      case SiStripDetId::TOB:
        return isNearEdgeTOB(localX, localY);
      case SiStripDetId::TEC:
        return isNearEdgeTEC(tTopo.tecRing(detId), localX, localY);
      default:
        edm::LogWarning("MuonTrackDeDxTableProducer") << "No subdetector found in isHitNearEdge, check for error";
        return false;
    }
  }

  float pfRelIso04(const pat::Muon& muon) {
    if (muon.pt() <= 0.f)
      return std::numeric_limits<float>::max();
    return (muon.pfIsolationR04().sumChargedHadronPt +
            std::max(0.f,
                     muon.pfIsolationR04().sumNeutralHadronEt + muon.pfIsolationR04().sumPhotonEt -
                         0.5f * muon.pfIsolationR04().sumPUPt)) /
           muon.pt();
  }

  bool passesGoodMuon(const pat::Muon& mu, float pfIso) {
    constexpr float
        kEtaMin = -1.5f,
        kEtaMax =
            1.5f;  // module edge hits do not contain a valid dE/dx measurement; this identification is not as clear for EC hence |eta| < 1.5.
    constexpr float kPFIsoMin = 0.f, kPFIsoMax = 0.15f;
    constexpr float kTimeMin = -10.f, kTimeMax = 25.f;  // favour massive particles
    constexpr float kTimeErrMin = 0.f, kTimeErrMax = 4.f;
    constexpr float kNDofMin = 8.f;
    constexpr float kInverseBetaMin = 0.5f;  // reject pathological (v > c) muons

    if (mu.eta() < kEtaMin || mu.eta() > kEtaMax)
      return false;
    if (!mu.isLooseMuon())
      return false;
    if (pfIso < kPFIsoMin || pfIso > kPFIsoMax)
      return false;
    if (!mu.isGlobalMuon())
      return false;
    if (mu.time().timeAtIpInOut < kTimeMin || mu.time().timeAtIpInOut > kTimeMax)
      return false;
    if (mu.time().timeAtIpInOutErr < kTimeErrMin || mu.time().timeAtIpInOutErr > kTimeErrMax)
      return false;
    if (mu.time().nDof < kNDofMin)
      return false;
    if (mu.inverseBeta() < kInverseBetaMin)
      return false;
    return true;
  }
}  // namespace

class MuonTrackDeDxTableProducer : public edm::global::EDProducer<> {
public:
  explicit MuonTrackDeDxTableProducer(const edm::ParameterSet&);
  ~MuonTrackDeDxTableProducer() override = default;
  static void fillDescriptions(edm::ConfigurationDescriptions&);

private:
  void produce(edm::StreamID, edm::Event&, const edm::EventSetup&) const override;

  const std::string name_;
  const edm::EDGetTokenT<std::vector<pat::Muon>> muonsToken_;
  const edm::EDGetTokenT<std::vector<pat::IsolatedTrack>> isoTracksToken_;
  const edm::EDGetTokenT<reco::DeDxHitInfoAss> dedxToken_;
  const edm::ESGetToken<TrackerTopology, TrackerTopologyRcd> trackerTopoToken_;
};

MuonTrackDeDxTableProducer::MuonTrackDeDxTableProducer(const edm::ParameterSet& iConfig)
    : name_(iConfig.getParameter<std::string>("name")),
      muonsToken_(consumes<std::vector<pat::Muon>>(iConfig.getParameter<edm::InputTag>("muons"))),
      isoTracksToken_(consumes<std::vector<pat::IsolatedTrack>>(iConfig.getParameter<edm::InputTag>("isolatedTracks"))),
      dedxToken_(consumes<reco::DeDxHitInfoAss>(iConfig.getParameter<edm::InputTag>("dedx"))),
      trackerTopoToken_(esConsumes()) {
  produces<nanoaod::FlatTable>(name_);
  produces<nanoaod::FlatTable>(name_ + "TrackDeDxHits");
  produces<nanoaod::FlatTable>(name_ + "TrackDeDxStrip");
  produces<nanoaod::FlatTable>(name_ + "TrackDeDxPixel");
}

void MuonTrackDeDxTableProducer::produce(edm::StreamID, edm::Event& iEvent, const edm::EventSetup& iSetup) const {
  edm::Handle<std::vector<pat::Muon>> muonsH;
  iEvent.getByToken(muonsToken_, muonsH);
  edm::Handle<std::vector<pat::IsolatedTrack>> isoTracksH;
  iEvent.getByToken(isoTracksToken_, isoTracksH);
  edm::Handle<reco::DeDxHitInfoAss> dedxH;
  iEvent.getByToken(dedxToken_, dedxH);

  const TrackerTopology& tTopo = iSetup.getData(trackerTopoToken_);

  // Map packedCandidate identity (ProductID, key) -> isolatedTracks index,
  // mirroring the identity IsolatedTrackCleaner itself matches on.
  std::unordered_map<std::pair<edm::ProductID, unsigned int>, size_t, PairHash> candToIsoIdx;
  candToIsoIdx.reserve(isoTracksH->size());
  for (size_t j = 0; j < isoTracksH->size(); ++j) {
    const auto& ref = (*isoTracksH)[j].packedCandRef();
    if (ref.isNonnull()) {
      candToIsoIdx[{ref.id(), ref.key()}] = j;
    }
  }

  const size_t nMuons = muonsH->size();

  // Per-muon extension columns
  std::vector<uint8_t> nDeDxHits(nMuons, 0);
  std::vector<uint8_t> nPixelDeDxHits(nMuons, 0);
  std::vector<bool> hasNearEdge(nMuons, false);

  // Per-hit columns (accumulated across all muons)
  std::vector<int16_t> hitMuonIdx;
  std::vector<float> hitDEdx;
  std::vector<float> hitPathLength;
  std::vector<uint8_t> hitLayer;
  std::vector<uint32_t> hitDetId;
  std::vector<bool> hitIsNearEdge;
  std::vector<int32_t> stripHitIdx, pixelHitIdx;
  std::vector<uint16_t> stripNumber, pixelRow, pixelColumn, pixelCharge;
  std::vector<uint8_t> stripAmplitude;

  // The "good muon" selection (fillHits) gates only which muons contribute rows to the MuonTrackDeDxHits per-hit
  // table; nDeDxHits, nPixelDeDxHits and trackHasHitNearEdge below are filled for every muon with a matched
  // isolatedTracks/DeDxHitInfo entry, independent of the selection.
  for (size_t i = 0; i < nMuons; ++i) {
    const pat::Muon& mu = (*muonsH)[i];

    const bool fillHits = passesGoodMuon(mu, pfRelIso04(mu));

    size_t matchedIdx = std::numeric_limits<size_t>::max();
    for (size_t k = 0; k < mu.numberOfSourceCandidatePtrs(); ++k) {
      const reco::CandidatePtr ptr = mu.sourceCandidatePtr(k);
      if (ptr.isNull())
        continue;
      auto it = candToIsoIdx.find({ptr.id(), ptr.key()});
      if (it != candToIsoIdx.end()) {
        matchedIdx = it->second;
        break;
      }
    }
    if (matchedIdx == std::numeric_limits<size_t>::max())
      continue;

    const reco::DeDxHitInfoRef dedxref = (*dedxH)[edm::Ref<std::vector<pat::IsolatedTrack>>(isoTracksH, matchedIdx)];
    if (dedxref.isNull())
      continue;

    const reco::DeDxHitInfo& dedx = *dedxref;
    // The hit counts saturate rather than wrap: a track cannot reach kMaxHitCount tracker hits, but a silent
    // wrap-around would be indistinguishable from a genuine low count if that ever changed.
    nDeDxHits[i] = static_cast<uint8_t>(std::min<size_t>(dedx.size(), kMaxHitCount));

    size_t nPixel = 0;
    bool nearEdge = false;

    for (size_t h = 0; h < dedx.size(); ++h) {
      const DetId dedxId = dedx.detId(h);
      const float localX = dedx.pos(h).x();
      const float localY = dedx.pos(h).y();
      const int subdet = dedxId.subdetId();

      if (isPixel(subdet))
        ++nPixel;

      const bool hitNearEdge = isHitNearEdge(tTopo, dedxId, localX, localY);
      if (hitNearEdge)
        nearEdge = true;

      if (fillHits) {
        if (hitDEdx.size() > static_cast<size_t>(std::numeric_limits<int32_t>::max()))
          throw cms::Exception("MuonTrackDeDxIndexOverflow") << "Hit index exceeds int32 range";
        const auto hitIdx = static_cast<int32_t>(hitDEdx.size());
        if (isPixel(subdet)) {
          const auto* cluster = dedx.pixelCluster(h);
          if (cluster == nullptr)
            throw cms::Exception("MissingMuonTrackDeDxCluster")
                << "Missing pixel cluster for muon " << i << ", source hit " << h << ", DetId " << dedxId.rawId();
          for (int channel = 0; channel < cluster->size(); ++channel) {
            const auto pixel = cluster->pixel(channel);
            pixelHitIdx.push_back(hitIdx);
            pixelRow.push_back(pixel.x);
            pixelColumn.push_back(pixel.y);
            pixelCharge.push_back(pixel.adc);
          }
        } else {
          const auto* cluster = dedx.stripCluster(h);
          if (cluster == nullptr)
            throw cms::Exception("MissingMuonTrackDeDxCluster")
                << "Missing strip cluster for muon " << i << ", source hit " << h << ", DetId " << dedxId.rawId();
          for (size_t channel = 0; channel < cluster->amplitudes().size(); ++channel) {
            const size_t strip = cluster->firstStrip() + channel;
            if (strip > std::numeric_limits<uint16_t>::max())
              throw cms::Exception("MuonTrackDeDxIndexOverflow") << "Strip index exceeds uint16 range";
            stripHitIdx.push_back(hitIdx);
            stripNumber.push_back(static_cast<uint16_t>(strip));
            stripAmplitude.push_back(cluster->amplitudes()[channel]);
          }
        }
        float charge;
        if (isPixel(subdet)) {
          charge = kMeVPerElectronHolePair * dedx.charge(h);
        } else {
          charge = kMeVPerElectronHolePair * kElectronsPerADCStrip * dedx.charge(h);
        }
        // dedx.pathlength() is filled in RECO (RecoTracker/DeDx/plugins/DeDxHitInfoProducer.cc) as the nominal
        // module thickness from the tracker geometry divided by |cos| of the local track incidence angle taken
        // from the fitted trajectory state on that module; it is copied unchanged into MiniAOD. It is stored
        // alongside dEdx so the geometric denominator can be undone or recalibrated downstream (e.g. the
        // effective-path-length correction applied in RecoTracker/DeDx/plugins/DeDxHitCalibrator.cc).
        hitDEdx.push_back(charge / dedx.pathlength(h));
        hitPathLength.push_back(dedx.pathlength(h));
        hitMuonIdx.push_back(static_cast<int16_t>(i));

        // Layer/disk/wheel index; 0 = unknown.
        uint8_t layer = 0;
        if (isPixel(subdet)) {
          if (subdet == PixelSubdetector::PixelBarrel)
            layer = static_cast<uint8_t>(tTopo.pxbLayer(dedxId));
          else
            layer = static_cast<uint8_t>(tTopo.pxfDisk(dedxId));
        } else {
          switch (SiStripDetId(dedxId).subDetector()) {
            case SiStripDetId::TIB:
              layer = static_cast<uint8_t>(tTopo.tibLayer(dedxId));
              break;
            case SiStripDetId::TID:
              layer = static_cast<uint8_t>(tTopo.tidWheel(dedxId));
              break;
            case SiStripDetId::TOB:
              layer = static_cast<uint8_t>(tTopo.tobLayer(dedxId));
              break;
            case SiStripDetId::TEC:
              layer = static_cast<uint8_t>(tTopo.tecWheel(dedxId));
              break;
            default:
              layer = 0;
          }
        }
        hitLayer.push_back(layer);
        hitDetId.push_back(dedxId.rawId());
        hitIsNearEdge.push_back(hitNearEdge);
      }
    }

    nPixelDeDxHits[i] = static_cast<uint8_t>(std::min<size_t>(nPixel, kMaxHitCount));
    hasNearEdge[i] = nearEdge;
  }

  // Build and put Muon extension table
  auto muTab = std::make_unique<nanoaod::FlatTable>(nMuons, name_, false, /*extension=*/true);
  muTab->addColumn<uint8_t>(
      "trackNDeDxHits",
      nDeDxHits,
      "number of dE/dx hits on the matched track; 0 if the muon has no matching isolatedTracks entry or no "
      "DeDxHitInfo");
  muTab->addColumn<uint8_t>("trackNPixelDeDxHits", nPixelDeDxHits, "number of pixel dE/dx hits");
  muTab->addColumn<bool>(
      "trackHasHitNearEdge", hasNearEdge, "any dE/dx hit near a sensor edge; false when trackNDeDxHits == 0");

  // Build and put per-hit table
  const size_t nHitsTotal = hitDEdx.size();
  auto hitTab = std::make_unique<nanoaod::FlatTable>(nHitsTotal, name_ + "TrackDeDxHits", false, false);
  hitTab->addColumn<int16_t>("muonIdx", hitMuonIdx, "index into the Muon collection");
  hitTab->addColumn<float>("dEdx", hitDEdx, "charge/pathlength [MeV/cm]", /*mantissaBits=*/12);
  hitTab->addColumn<float>("pathLength",
                           hitPathLength,
                           "path length used in the dE/dx denominator [cm]: nominal sensor thickness from the "
                           "tracker geometry divided by |cos| of the local track incidence angle (straight-line "
                           "crossing of the module, not an entry-to-exit reconstruction)",
                           /*mantissaBits=*/12);
  hitTab->addColumn<uint8_t>("layer", hitLayer, "pixel layer/disk or strip layer/wheel, 0 if unknown");
  hitTab->addColumn<uint32_t>("detId", hitDetId, "raw DetId");
  hitTab->addColumn<bool>("isHitNearEdge",
                          hitIsNearEdge,
                          "hit is within the sensor-edge fiducial region (EXO-19-006), i.e. its dE/dx measurement "
                          "is not reliable");

  auto stripTab = std::make_unique<nanoaod::FlatTable>(stripHitIdx.size(), name_ + "TrackDeDxStrip", false, false);
  stripTab->addColumn<int32_t>("hitIdx", stripHitIdx, "event-local row in MuonTrackDeDxHits");
  stripTab->addColumn<uint16_t>("strip", stripNumber, "sensor strip index: cluster firstStrip plus amplitude index");
  stripTab->addColumn<uint8_t>(
      "amplitude", stripAmplitude, "stored strip ADC code, including zero; 254 and 255 are overflow codes");
  auto pixelTab = std::make_unique<nanoaod::FlatTable>(pixelHitIdx.size(), name_ + "TrackDeDxPixel", false, false);
  pixelTab->addColumn<int32_t>("hitIdx", pixelHitIdx, "event-local row in MuonTrackDeDxHits");
  pixelTab->addColumn<uint16_t>("row", pixelRow, "pixel sensor row");
  pixelTab->addColumn<uint16_t>("column", pixelColumn, "pixel sensor column");
  pixelTab->addColumn<uint16_t>("charge", pixelCharge, "stored calibrated pixel charge [electrons], not raw ADC");

  iEvent.put(std::move(stripTab), name_ + "TrackDeDxStrip");
  iEvent.put(std::move(pixelTab), name_ + "TrackDeDxPixel");
  iEvent.put(std::move(muTab), name_);
  iEvent.put(std::move(hitTab), name_ + "TrackDeDxHits");
}

void MuonTrackDeDxTableProducer::fillDescriptions(edm::ConfigurationDescriptions& descriptions) {
  edm::ParameterSetDescription desc;
  desc.add<std::string>("name", "Muon")
      ->setComment("name of the Muon FlatTable being extended (also prefixes the hit table)");
  desc.add<edm::InputTag>("muons", edm::InputTag("linkedObjects", "muons"))
      ->setComment("PAT muon collection (row identity and order match the Muon main table)");
  desc.add<edm::InputTag>("isolatedTracks", edm::InputTag("isolatedTracks"))
      ->setComment("full (uncleaned) isolated track collection used for packedCandidate identity matching");
  desc.add<edm::InputTag>("dedx", edm::InputTag("isolatedTracks"))
      ->setComment("DeDxHitInfo association product (same label as isolatedTracks)");
  descriptions.add("muonTrackDeDxTable", desc);
}

DEFINE_FWK_MODULE(MuonTrackDeDxTableProducer);
